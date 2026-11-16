# Extending a diagram from representatives

Let $P(x)$ be a merely inhabited type of representatives for each object $x$ of $B$. A diagram $F$ is given on the bicategory of pairs $(x,p)$, whose hom from $(x,p)$ to $(y,q)$ is $B(x,y)$. We will extend $F$ to $B$. The construction starts on finite lists of objects. One object determines an object value, two determine a hom functor, and three determine a compositor.

```agda
module Bicategories.WeakBiequivalence.Descent.Object where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Base using (ℕ; _+_)
open import Cubical.Data.SumFin.Base using (Fin; fzero; fsuc)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Category.Base hiding (isUnivalent)
open import Cubical.Categories.Functor.Base
open import Bicategories.Base
open import Bicategories.FullSubbicategory
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Path
open import Bicategories.Pseudofunctor.Univalence
open import Bicategories.Univalence using (isUnivalent)
open import Bicategories.WeakBiequivalence.Descent.Pullback
open import Bicategories.WeakBiequivalence.Descent.Reindex
open import Bicategories.WeakBiequivalence.Descent.Finite

open import Bicategories.WeakBiequivalence.Descent.Tuples

module ObjectDescent {o h c d e f p} (B : Bicategory o h c) (D : Bicategory d e f)
  (uD : isUnivalent D) (P : Bicategory.Ob B → Type p) (cover : (x : _) → PT.∥ P x ∥₁)
  (F : Pseudofunctor (reindex B (fst {B = P})) D) where

  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F
  open Pseudofunctor
```

For any finite list $v$, restrict the given diagram to representatives of that list. The type $\operatorname{Ext}(v)$ consists of extensions, each given by a diagram on the list together with an equality after restriction back to its representatives. This is a fiber of the finite restriction equivalence, hence contractible. Its center gives a specific extension, and contractibility later identifies the choices made on overlapping lists.

```agda
  module Finite {n} (v : Fin n → B.Ob) where
    diagram = restrict B fst (λ (s : Σ (Fin n) (λ i → P (v i))) → v (s .fst) , s .snd) F

    Ext = fiber (restrict B v (fst {B = λ i → P (v i)})) diagram

    opaque
      contr : isContr Ext
      contr = isEquivFiniteProjection B D v (λ i → P (v i)) (λ i → cover (v i))
        (λ F G → transformationToPath uD {F = F} {G = G}) .isEquiv.equiv-proof diagram

    restrictExt : ∀ {k} (a : Fin k → Fin n) → Ext →
      fiber (restrict B (λ i → v (a i)) (fst {B = λ i → P (v (a i))}))
        (restrict B fst (λ (s : Σ (Fin k) (λ i → P (v (a i)))) → v (a (s .fst)) , s .snd) F)
    restrictExt a (E , q) .fst = restrict B v a E
    restrictExt a (E , q) .snd i =
      restrict B (λ z → v (z .fst)) (λ z → a (z .fst) , z .snd) (q i)
```

Apply this to the one-element list containing $x$. Evaluating its extension gives an object of $D$ and, for each $p:P(x)$, a path to $F(x,p)$. We keep these paths with the object so that subsequent hom functors and comparison cells can be related to those of $F$.

```agda
  Obj : B.Ob → Type _
  Obj x = Σ[ z ∈ D.Ob ] ((r : P x) → z ≡ F.F₀ (x , r))

  module _ {n} {v : Fin n → B.Ob} where
    atObject : Finite.Ext v → (i : Fin n) → Obj (v i)
    atObject (E , q) i = E .F₀ i , λ r j → q j .F₀ (i , r)

  object : (x : B.Ob) → Obj x
  object x = atObject {v = λ (_ : Fin 1) → x} (Finite.contr _ .fst) i₀
```

For a pair of objects we also align the one-object restrictions with the chosen one-object extensions. These alignments live in contractible fibers. Transport along them adjusts both the endpoints of the hom functor and its comparison on every pair of representatives.

```agda
  module Aligned {n} (v : Fin n → B.Ob) where
    Alignment : Finite.Ext v → Type _
    Alignment E = (i : Fin n) → Finite.restrictExt v (λ (_ : Fin 1) → i) E
                               ≡ Finite.contr (λ _ → v i) .fst
    Ext = Σ (Finite.Ext v) Alignment

    opaque
      contr : isContr Ext
      contr = isContrΣ (Finite.contr v) λ E → isContrΠ λ i →
        isContr→isContrPath (Finite.contr (λ _ → v i)) _ _

    restrictExt : ∀ {k} (a : Fin k → Fin n) (E : Ext) →
      Σ[ F′ ∈ Finite.Ext (λ i → v (a i)) ]
      ((i : Fin k) → Finite.restrictExt (λ j → v (a j)) (λ (_ : Fin 1) → i) F′
                   ≡ Finite.contr (λ _ → v (a i)) .fst)
    restrictExt a (E , q) = Finite.restrictExt v a E , λ i → q (a i)

    objLine : (E : Ext) (i : Fin n) → atObject {v = v} (E .fst) i ≡ object (v i)
    objLine E i j = atObject {v = λ (_ : Fin 1) → v i} (E .snd i j) i₀

  Hom : {x y : B.Ob} → Obj x → Obj y → Type _
  Hom {x} {y} X Y = Σ[ H ∈ Functor (B.hom x y) (D.hom (X .fst) (Y .fst)) ]
    ((r : P x) (s : P y) → PathP (λ j → Functor (B.hom x y)
      (D.hom (X .snd r j) (Y .snd s j))) H (F.Fₕ (x , r) (y , s)))

  module Normalize {n} (v : Fin n → B.Ob) (E : Aligned.Ext v) where
    open Aligned v using (objLine)
    O = objLine E
    private
      G = E .fst .fst
      q = E .fst .snd

    rawHom : (i j : Fin n) → Hom {x = v i} {v j} (O i i0) (O j i0)
    rawHom i j = G .Fₕ i j , (λ r s t → q t .Fₕ (i , r) (j , s))

    homLine : (i j : Fin n) → PathP (λ t → Hom {x = v i} {v j} (O i t) (O j t))
      (rawHom i j) (transport (λ t → Hom {x = v i} {v j} (O i t) (O j t)) (rawHom i j))
    homLine i j = transport-filler _ (rawHom i j)

  homPair : (v : Fin 2 → B.Ob) → Hom (object (v i₀)) (object (v i₁))
  homPair v = Normalize.homLine v (Aligned.contr v .fst) i₀ i₁ i1

  hom : (x y : B.Ob) → Hom (object x) (object y)
  hom x y = homPair (two x y)

  module Ready {n} (v : Fin n → B.Ob) (E : Aligned.Ext v) where
    open Normalize v E public

    homAlignment : (i j : Fin n) → homLine i j i1 ≡ hom (v i) (v j)
    homAlignment i j =
      cong (λ e → Normalize.homLine pair e i₀ i₁ i1)
           (isContr→isProp (Aligned.contr pair) (Aligned.restrictExt v (two i j) E) (Aligned.contr pair .fst))
      ∙ (λ t → homPair (twoη pair t))
      where
      pair = λ k → v (two i j k)
```

The units and compositors involve at most three objects. On the corresponding finite family, first transport each comparison along the paths of its endpoints, then along the paths of its hom functors. Including the comparison with the original diagram in the transported type supplies the same computation rule at every representative.

```agda
  UnitDatum : {x : B.Ob} (X : Obj x) → Hom X X → Type _
  UnitDatum {x} X H = Σ[ u ∈ CatIso (D.hom (X .fst) (X .fst))
                              (D.id₁ (X .fst)) (H .fst ⟅ B.id₁ x ⟆) ]
    ((r : P x) → PathP (λ i → CatIso (D.hom (X .snd r i) (X .snd r i))
                  (D.id₁ (X .snd r i)) (H .snd r r i ⟅ B.id₁ x ⟆)) u (F.unit (x , r)))

  module _ {x y z : B.Ob} (X : Obj x) (Y : Obj y) (Z : Obj z) where
    CompDatum : Hom X Y → Hom Y Z → Hom X Z → Type _
    CompDatum H K L = Σ[ m ∈ ((f : B.Cell x y) (g : B.Cell y z) →
      CatIso (D.hom (X .fst) (Z .fst)) ((H .fst ⟅ f ⟆) D.⋆₁ (K .fst ⟅ g ⟆))
              (L .fst ⟅ f B.⋆₁ g ⟆)) ]
      ((r : P x) (s : P y) (t : P z) → PathP (λ i → (f : B.Cell x y) (g : B.Cell y z) →
        CatIso (D.hom (X .snd r i) (Z .snd t i))
          ((H .snd r s i ⟅ f ⟆) D.⋆₁ (K .snd s t i ⟅ g ⟆)) (L .snd r t i ⟅ f B.⋆₁ g ⟆))
        m (F.compositor {x , r} {y , s} {z , t}))

  module Comparisons {n} (v : Fin n → B.Ob) (E : Aligned.Ext v) where
    open Ready v E

    private
      G = E .fst .fst
      q = E .fst .snd

    normalizedUnit : (i : Fin n) → UnitDatum (object (v i)) (hom (v i) (v i))
    normalizedUnit i = transport (λ t → UnitDatum (object (v i)) (homAlignment i i t))
      (transport (λ t → UnitDatum (O i t) (homLine i i t))
        (G .unit i , (λ p t → q t .unit (i , p))))

    normalizedComp : (i j k : Fin n) → CompDatum (object (v i)) (object (v j)) (object (v k))
      (hom (v i) (v j)) (hom (v j) (v k)) (hom (v i) (v k))
    normalizedComp i j k =
      transport (λ t → CompDatum (object (v i)) (object (v j)) (object (v k))
        (homAlignment i j t) (homAlignment j k t) (homAlignment i k t))
      (transport (λ t → CompDatum (O i t) (O j t) (O k t)
        (homLine i j t) (homLine j k t) (homLine i k t))
        (G .compositor {i} {j} {k} , (λ p r s t → q t .compositor {i , p} {j , r} {k , s})))

  opaque
    unitAt : (x : B.Ob) → UnitDatum (object x) (hom x x)
    unitAt x = Comparisons.normalizedUnit (λ (_ : Fin 1) → x) (Aligned.contr _ .fst) i₀

    compAt : (x y z : B.Ob) → CompDatum (object x) (object y) (object z)
      (hom x y) (hom y z) (hom x z)
    compAt x y z = Comparisons.normalizedComp (three x y z) (Aligned.contr _ .fst) i₀ i₁ i₂
```

The pseudofunctor laws are equations in hom-sets. For each law one may therefore choose representatives for its endpoints under truncation. At these representatives the four parts of the extended diagram give a line from the equation in the extension to the equation for the original diagram. Transport along this line proves the law.

```agda
  private
    module At {n} (v : Fin n → B.Ob) (r : (i : Fin n) → P (v i)) (t : I) where
      ob : (i : Fin n) → D.Ob
      ob i = object (v i) .snd (r i) t

      H : (i j : Fin n) → Functor (B.hom (v i) (v j)) (D.hom (ob i) (ob j))
      H i j = hom (v i) (v j) .snd (r i) (r j) t

      U : (i : Fin n) → CatIso (D.hom (ob i) (ob i)) (D.id₁ (ob i))
        (H i i ⟅ B.id₁ (v i) ⟆)
      U i = unitAt (v i) .snd (r i) t

      C : (i j k : Fin n) (f : B.Cell (v i) (v j)) (g : B.Cell (v j) (v k))
        → CatIso (D.hom (ob i) (ob k))
          ((H i j ⟅ f ⟆) D.⋆₁ (H j k ⟅ g ⟆)) (H i k ⟅ f B.⋆₁ g ⟆)
      C i j k = compAt (v i) (v j) (v k) .snd (r i) (r j) (r k) t

      Natural : (i j k : Fin n) {f f′ : B.Cell (v i) (v j)} {g g′ : B.Cell (v j) (v k)}
        (α : B.Two f f′) (β : B.Two g g′) → Type _
      Natural i j k {f} {f′} {g} {g′} α β =
        (((H i j ⟪ α ⟫) D.⊗ (H j k ⟪ β ⟫)) D.⋆₂ C i j k f′ g′ .fst)
        ≡ (C i j k f g .fst D.⋆₂ (H i k ⟪ α B.⊗ β ⟫))

      Left Right : (i j : Fin n) (f : B.Cell (v i) (v j)) → Type _
      Left i j f =
        (((U i .fst D.▷ (H i j ⟅ f ⟆)) D.⋆₂ C i i j (B.id₁ (v i)) f .fst)
          D.⋆₂ (H i j ⟪ B.leftUnitor f .fst ⟫)) ≡ D.leftUnitor (H i j ⟅ f ⟆) .fst
      Right i j f =
        ((((H i j ⟅ f ⟆) D.◁ U j .fst) D.⋆₂ C i j j f (B.id₁ (v j)) .fst)
          D.⋆₂ (H i j ⟪ B.rightUnitor f .fst ⟫)) ≡ D.rightUnitor (H i j ⟅ f ⟆) .fst

      Assoc : (i j k l : Fin n) (f : B.Cell (v i) (v j))
        (g : B.Cell (v j) (v k)) (h : B.Cell (v k) (v l)) → Type _
      Assoc i j k l f g h =
        (((C i j k f g .fst D.▷ (H k l ⟅ h ⟆)) D.⋆₂ C i k l (f B.⋆₁ g) h .fst)
          D.⋆₂ (H i l ⟪ B.associator f g h .fst ⟫))
        ≡ ((D.associator (H i j ⟅ f ⟆) (H j k ⟅ g ⟆) (H k l ⟅ h ⟆) .fst
           D.⋆₂ ((H i j ⟅ f ⟆) D.◁ C j k l g h .fst)) D.⋆₂ C i j l f (g B.⋆₁ h) .fst)

    withReps : ∀ {ℓ n} (v : Fin n → B.Ob) {T : Type ℓ} → isProp T
      → (((i : Fin n) → P (v i)) → T) → T
    withReps v prop k = PT.rec prop k (chooseFinite (λ i → P (v i)) (λ i → cover (v i)))

  extension : Pseudofunctor B D
  extension .F₀ x = object x .fst
  extension .Fₕ x y = hom x y .fst
  extension .unit x = unitAt x .fst
  extension .compositor {x} {y} {z} = compAt x y z .fst
  extension .compositor-natural {x} {y} {z} α β =
    withReps v (Category.isSetHom (D.hom _ _) _ _) λ r →
      transport (λ t → At.Natural v r (~ t) i₀ i₁ i₂ α β)
        (F.compositor-natural {x , r i₀} {y , r i₁} {z , r i₂} α β)
    where v = three x y z
  extension .leftUnitor-law {x} {y} f =
    withReps v (Category.isSetHom (D.hom _ _) _ _) λ r →
      transport (λ t → At.Left v r (~ t) i₀ i₁ f)
        (F.leftUnitor-law {x , r i₀} {y , r i₁} f)
    where v = two x y
  extension .rightUnitor-law {x} {y} f =
    withReps v (Category.isSetHom (D.hom _ _) _ _) λ r →
      transport (λ t → At.Right v r (~ t) i₀ i₁ f)
        (F.rightUnitor-law {x , r i₀} {y , r i₁} f)
    where v = two x y
  extension .associator-law {w} {x} {y} {z} f g h =
    withReps v (Category.isSetHom (D.hom _ _) _ _) λ r →
      transport (λ t → At.Assoc v r (~ t) i₀ i₁ i₂ i₃ f g h)
        (F.associator-law {w , r i₀} {x , r i₁} {y , r i₂} {z , r i₃} f g h)
    where v = four w x y z
```

The comparisons on representatives assemble into a path of pseudofunctors. Its projections on objects, homs, units, and compositors are precisely the four computation rules.

```agda
  opaque
    restrictExtension : pull (fst {B = P}) extension ≡ F
    restrictExtension = pseudofunctorPath {F = pull (fst {B = P}) extension} {G = F}
      (λ i (x , r) → object x .snd r i)
      (λ i (x , r) (y , s) → hom x y .snd r s i)
      (λ i (x , r) → unitAt x .snd r i)
      (λ i { (x , r) } { (y , s) } { (z , t) } → compAt x y z .snd r s t i)
```
