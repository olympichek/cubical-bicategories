# Structure identity for univalent bicategories

Here we prove that a weak biequivalence identifies two univalent bicategories. The proof builds an equality of records, starting with their object types and hom-categories and accounting for each field of the bicategory structure.

```agda
module Bicategories.StructureIdentity where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path using (symIso)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToEquiv)
open import Cubical.Foundations.Univalence using (univalence)
open import Cubical.Data.Sigma
open import Bicategories.StructureIdentity.RecordFields
open import Cubical.Categories.Category.Base as Cat hiding (isUnivalent)
import Cubical.Categories.Category.Base as C
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.Univalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Composition using (_∘P_; compIdLeft)
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.WeakBiequivalence.Properties

```

For a weak biequivalence $F:B\to D$ between univalent bicategories at the same levels, we want the equality of bicategories to remember *which* comparison produced it. We therefore prove a path of pairs
$$
(B,\mathrm{id}_B)=(D,F)
\quad\text{in}\quad
\sum_{X:\mathrm{Bicategory}}\operatorname{PsFun}(B,X).
$$
Its first projection will identify $B$ with $D$. Its second will let us transport a particular pseudofunctor into $B$ along that identification.

```agda
PointedComparison : ∀ {o h c} {B D : Bicategory o h c} → Pseudofunctor B D → Type _
PointedComparison {o} {h} {c} {B} {D} F =
  Path (Σ (Bicategory o h c) (Pseudofunctor B)) (B , idPseudofunctor B) (D , F)

private
  unquoteDecl structureFields = declareFields structureFields (quote BicategoryStructure)
  unquoteDecl pseudoFields = declareFields pseudoFields (quote Pseudofunctor)
  open Iso

  Tail₂ : ∀ {l m n r} {R : Type r} {A : Type l} {B : A → Type m}
    {C : (a : A) → B a → Type n} → Iso R (Σ A (λ a → Σ (B a) (C a)))
    → (a : A) → B a → Type n
  Tail₂ {C = C} _ = C

  Tail₄ : ∀ {l m n r t u} {R : Type u} {A : Type l} {B : A → Type m}
    {C : (a : A) → B a → Type n} {D : ∀ a b → C a b → Type r}
    {E : ∀ a b c → D a b c → Type t}
    → Iso R (Σ A (λ a → Σ (B a) (λ b → Σ (C a b) (λ c → Σ (D a b c) (E a b c)))))
    → ∀ a b c → D a b c → Type t
  Tail₄ {E = E} _ = E

  pack : ∀ {o h c} (X : Type o) (H : X → X → Category h c)
       → BicategoryStructure X H → Bicategory o h c
  pack X H S .Bicategory.Ob = X
  pack X H S .Bicategory.hom = H
  pack X H S .Bicategory.structure = S

```

A recurring step is to reduce a choice to a single case. If choosing data $Q(x)$ is equivalent to specifying a path $a=x$, then $\sum_x Q(x)$ is contractible, with the reflexive choice as center. For a fixed univalent hom-category $C$, ordinary structure identity applies this observation to a target univalent category equipped with a weak equivalence from $C$.

```agda
  singleton : ∀ {l m} {A : Type l} (a : A) {Q : A → Type m}
            → ((x : A) → (a ≡ x) ≃ Q x) → isContr (Σ A Q)
  singleton a e = isOfHLevelRespectEquiv 0 (Σ-cong-equiv-snd e) (isContrSingl a)

  univalentHomSingleton : ∀ {h c} (C : Category h c) (u : C.isUnivalent C)
    → isContr (Σ[ D ∈ Category h c ] (C.isUnivalent D × WeakEquivalence C D))
  univalentHomSingleton {h} {c} C u = isContrRetract
    (λ (D , v , w) → (D , v) , w) (λ ((D , v) , w) → D , v , w) (λ _ → refl)
    (singleton (C , u) (λ (D , v) → invEquiv (Σ≡PropEquiv (λ _ → C.isPropIsUnivalent))
                                  ∙ₑ invEquiv (WeakEquivalence≃Path u v)))

  module Identity {o h c} (B : Bicategory o h c) (localB : isLocallyUnivalent B) where
    module B = Bicategory B

    OperatorData =
      ((x : B.Ob) → Σ[ t ∈ B.Cell x x ] CatIso (B.hom x x) t (B.id₁ x))
      × ((x y z : B.Ob) → Σ[ m ∈ Functor (B.hom x y ×C B.hom y z) (B.hom x z) ]
                          NatIso m B.comp)

    canonicalOps : OperatorData
    canonicalOps = (λ x → B.id₁ x , idCatIso) , (λ x y z → B.comp , idNatIso B.comp)

    operatorDataContr : isContr OperatorData
    operatorDataContr = isContrΣ
      (isContrΠ λ x → singleton (B.id₁ x)
        (λ t → isoToEquiv symIso ∙ₑ C.isUnivalent.univEquiv (localB x x) t (B.id₁ x)))
      (λ _ → isContrΠ λ x → isContrΠ λ y → isContrΠ λ z → singleton B.comp
        (λ m → isoToEquiv symIso ∙ₑ Path≃NatIso (localB x z)))

```

Fix the object type and hom-categories for the moment. `operatorDataContr` says that an identity arrow equipped with an isomorphism to the original identity has a unique choice up to path. The same holds for a composition functor equipped with a natural isomorphism to the original one. Keeping those isomorphisms in the data lets `Ops` reconstruct the pseudofunctor whose laws we will use.

```agda
    module Ops (d : OperatorData) where
      identity : (x : B.Ob) → B.Cell x x
      identity x = d .fst x .fst
      horizontal : ∀ {x y z} → Functor (B.hom x y ×C B.hom y z) (B.hom x z)
      horizontal {x} {y} {z} = d .snd x y z .fst

      Rest = Tail₂ (structureFields {Ob = B.Ob} {hom = B.hom}) identity horizontal

      module _ (s : Rest) where
        target = pack B.Ob B.hom (inv structureFields (identity , horizontal , s))
        private module D = Bicategory target

        comparison : ∀ {x y z} (f : B.Cell x y) (g : B.Cell y z)
                   → CatIso (B.hom x z) (f D.⋆₁ g) (f B.⋆₁ g)
        comparison {x} {y} {z} f g =
          NatTrans.N-ob (NatIso.trans n) (f , g) , NatIso.nIso n (f , g)
          where n = d .snd x y z .snd

        Laws = Tail₄ (pseudoFields {B = B} {D = target}) (λ x → x) (λ x y → Id)
                     (λ x → d .fst x .snd) comparison

        action : Laws → Pseudofunctor B target
        action l = inv pseudoFields ((λ x → x) , (λ x y → Id) ,
                     (λ x → d .fst x .snd) , comparison , l)

    OperatorGoal : OperatorData → Type _
    OperatorGoal d = (s : Ops.Rest d) (l : Ops.Laws d s) → PointedComparison (Ops.action d s l)
```

The two operations and their comparison isomorphisms vary in contractible types. At their common center the comparison on each operation is the identity. The left and right unitor laws give paths of the unitor isomorphisms. Cancelling identity 2-cells in the associator law gives the path of associators. Each residual naturality or coherence equation belongs to a proposition.

```agda
    module Normal (s : Ops.Rest canonicalOps) (laws : Ops.Laws canonicalOps s) where
      private
        D = Ops.target canonicalOps s
        module D = Bicategory D
        P : Pseudofunctor B D
        P = inv pseudoFields ((λ x → x) , (λ x y → Id) , (λ _ → idCatIso) ,
                             (λ f g → idCatIso) , laws)
        module P = Pseudofunctor P
        module I = Pseudofunctor (idPseudofunctor B)

        eraseIds : ∀ {x y} {a b : B.Cell x y} (p : B.Two a b) {q : B.Two b b}
                 → q ≡ B.id₂ b → (p B.⋆₂ q) B.⋆₂ B.id₂ b ≡ p
        eraseIds {x} {y} p e =
          Category.⋆IdR (B.hom x y) _ ∙ cong₂ B._⋆₂_ refl e ∙ Category.⋆IdR (B.hom x y) p

        L : ∀ {x y} (f : B.Cell x y) → B.leftUnitor f ≡ D.leftUnitor f
        L f = CatIso≡ _ _ (sym (I.leftUnitor-law f) ∙ P.leftUnitor-law f)
        R : ∀ {x y} (f : B.Cell x y) → B.rightUnitor f ≡ D.rightUnitor f
        R f = CatIso≡ _ _ (sym (I.rightUnitor-law f) ∙ P.rightUnitor-law f)
        A : ∀ {v w x y} (f : B.Cell v w) (g : B.Cell w x) (k : B.Cell x y)
          → B.associator f g k ≡ D.associator f g k
        A f g k = CatIso≡ _ _
          (sym (eraseIds _ (Functor.F-id B.comp)) ∙ sym (I.associator-law f g k)
           ∙ P.associator-law f g k ∙ eraseIds _ (Functor.F-id B.comp))

        open B using (_⋆₂_; _⋆₁_; _◁_; _▷_; _⊗_; id₁)

```

The paths $L$, $R$ and $A$ now identify the unitors and associator. For the triangle, for example, these paths give the two moving edges of a square whose endpoints are the triangle proofs in $B$ and $D$. The square fills because 2-cells between fixed arrows form a set. The following record path uses the same argument for each remaining equation.

```agda
      path : B ≡ D
      path i .Bicategory.Ob = B.Ob
      path i .Bicategory.hom = B.hom
      path i .Bicategory.structure .BicategoryStructure.id₁ = B.id₁
      path i .Bicategory.structure .BicategoryStructure.comp = B.comp
      path i .Bicategory.structure .BicategoryStructure.leftUnitor f = L f i
      path i .Bicategory.structure .BicategoryStructure.rightUnitor f = R f i
      path i .Bicategory.structure .BicategoryStructure.associator f g k = A f g k i
      path i .Bicategory.structure .BicategoryStructure.leftUnitor-natural {x} {y} {f} {g} α =
        isSet→SquareP (λ _ _ → Category.isSetHom (B.hom x y))
          (B.leftUnitor-natural α) (D.leftUnitor-natural α)
          (λ j → id₁ x ◁ α ⋆₂ L g j .fst) (λ j → L f j .fst ⋆₂ α) i
      path i .Bicategory.structure .BicategoryStructure.rightUnitor-natural {x} {y} {f} {g} α =
        isSet→SquareP (λ _ _ → Category.isSetHom (B.hom x y))
          (B.rightUnitor-natural α) (D.rightUnitor-natural α)
          (λ j → α ▷ id₁ y ⋆₂ R g j .fst) (λ j → R f j .fst ⋆₂ α) i
      path i .Bicategory.structure .BicategoryStructure.associator-natural
          {w} {z = z} {f} {f'} {g} {g'} {k} {k'} α β γ =
        isSet→SquareP (λ _ _ → Category.isSetHom (B.hom w z))
          (B.associator-natural α β γ) (D.associator-natural α β γ)
          (λ j → ((α ⊗ β) ⊗ γ) ⋆₂ A f' g' k' j .fst) (λ j → A f g k j .fst ⋆₂ (α ⊗ (β ⊗ γ))) i
      path i .Bicategory.structure .BicategoryStructure.triangle {x} {y} {z} f g =
        isSet→SquareP (λ _ _ → Category.isSetHom (B.hom x z)) (B.triangle f g) (D.triangle f g)
          (λ j → A f (id₁ y) g j .fst ⋆₂ f ◁ L g j .fst) (λ j → R f j .fst ▷ g) i
      path i .Bicategory.structure .BicategoryStructure.pentagon {v} {z = z} f g k l =
        isSet→SquareP (λ _ _ → Category.isSetHom (B.hom v z))
          (B.pentagon f g k l) (D.pentagon f g k l)
          (λ j → A (f ⋆₁ g) k l j .fst ⋆₂ A f g (k ⋆₁ l) j .fst)
          (λ j → A f g k j .fst ▷ l ⋆₂ A f (g ⋆₁ k) l j .fst ⋆₂ f ◁ A g k l j .fst) i
      path i .Bicategory.structure .BicategoryStructure.unitors-id x =
        isSet→SquareP (λ _ _ → Category.isSetHom (B.hom x x)) (B.unitors-id x) (D.unitors-id x)
          (λ j → L (id₁ x) j .fst) (λ j → R (id₁ x) j .fst) i

      pointed : PointedComparison P
      pointed i .fst = path i
      pointed i .snd .Pseudofunctor.F₀ x = x
      pointed i .snd .Pseudofunctor.Fₕ x y = Id
      pointed i .snd .Pseudofunctor.unit x = idCatIso
      pointed i .snd .Pseudofunctor.compositor f g = idCatIso
      pointed i .snd .Pseudofunctor.compositor-natural {x} {z = z} α β =
        isSet→SquareP (λ _ _ → Category.isSetHom (B.hom x z))
          (I.compositor-natural α β) (P.compositor-natural α β) refl refl i
      pointed i .snd .Pseudofunctor.leftUnitor-law {x} {y} f =
        isSet→SquareP (λ _ _ → Category.isSetHom (B.hom x y))
          (I.leftUnitor-law f) (P.leftUnitor-law f) refl (λ j → L f j .fst) i
      pointed i .snd .Pseudofunctor.rightUnitor-law {x} {y} f =
        isSet→SquareP (λ _ _ → Category.isSetHom (B.hom x y))
          (I.rightUnitor-law f) (P.rightUnitor-law f) refl (λ j → R f j .fst) i
      pointed i .snd .Pseudofunctor.associator-law {w} {z = z} f g k =
        isSet→SquareP (λ _ _ → Category.isSetHom (B.hom w z))
          (I.associator-law f g k) (P.associator-law f g k) refl
          (λ j → (A f g k j .fst ⋆₂ (f ◁ B.id₂ _)) ⋆₂ B.id₂ _) i

    compareOperators : ∀ d → OperatorGoal d
    compareOperators d = subst OperatorGoal (isContr→isProp operatorDataContr canonicalOps d)
                               Normal.pointed
```

It remains to reduce the comparison to one acting by identities on objects and hom-categories. Univalence of types makes the family of object carriers with a specified equivalence contractible. At the identity object carrier, the corresponding family of hom-categories is contractible by structure identity for univalent categories, applied independently at every pair of objects.

```agda
    ObjectData = Σ[ X ∈ Type o ] B.Ob ≃ X
    objectCenter : ObjectData
    objectCenter = B.Ob , idEquiv B.Ob

    HomData : ObjectData → Type _
    HomData (X , e) = Σ[ H ∈ (X → X → Category h c) ] ((x y : B.Ob)
      → C.isUnivalent (H (e .fst x) (e .fst y)) × WeakEquivalence (B.hom x y) (H (e .fst x) (e .fst y)))

    Graph = Σ ObjectData HomData
    graphCenter : Graph
    graphCenter = objectCenter , B.hom , λ x y → localB x y ,
      weakEquivalence Id (isWeakBiequivalenceId B .fst x y)

    graphContr : isContr Graph
    graphContr = isContrΣ'
      (objectCenter , isContr→isProp (singleton B.Ob (λ _ → univalence)) objectCenter)
      (isContrRetract (λ (H , p) x y → H x y , p x y)
                      (λ t → (λ x y → t x y .fst) , (λ x y → t x y .snd))
                      (λ _ → refl)
                      (isContrΠ λ x → isContrΠ λ y → univalentHomSingleton (B.hom x y) (localB x y)))

    GraphGoal : Graph → Type _
    GraphGoal ((X , e) , H , local) = (S : BicategoryStructure X H)
      → (rest : Tail₂ (pseudoFields {B = B} {D = pack X H S}) (e .fst)
                   (λ x y → WeakEquivalence.func (local x y .snd)))
      → PointedComparison (inv (pseudoFields {B = B} {D = pack X H S})
          (e .fst , (λ x y → WeakEquivalence.func (local x y .snd)) , rest))

```

At `graphCenter` the object map and every hom functor are identities. The pseudofunctor’s unit is therefore precisely the isomorphism comparing the two identity arrows. Its compositor and naturality assemble into the natural isomorphism comparing the composition functors. These are the inputs `compareOperators` needs.

```agda
    graphCenterPath : GraphGoal graphCenter
    graphCenterPath S dataOfMap =
      compareOperators operators (fun structureFields S .snd .snd)
        (fun pseudoFields F .snd .snd .snd .snd)
      ∙ straighten
      where
      D = pack B.Ob B.hom S
      module D = Bicategory D
      F : Pseudofunctor B D
      F = inv pseudoFields ((λ x → x) , (λ x y → Id) , dataOfMap)
      module F = Pseudofunctor F

      compIso : ∀ x y z → NatIso (D.comp {x} {y} {z}) B.comp
      compIso x y z .NatIso.trans .NatTrans.N-ob (f , g) = F.compositor f g .fst
      compIso x y z .NatIso.trans .NatTrans.N-hom (α , β) = F.compositor-natural α β
      compIso x y z .NatIso.nIso (f , g) = F.compositor f g .snd

      operators : OperatorData
      operators = (λ x → D.id₁ x , F.unit x) , (λ x y z → D.comp , compIso x y z)
      straighten : Path (Σ (Bicategory o h c) (Pseudofunctor B))
        (_ , Ops.action operators (fun structureFields S .snd .snd) (fun pseudoFields F .snd .snd .snd .snd))
        (D , F)
      straighten i .fst = pack B.Ob B.hom (ret structureFields S i)
      straighten i .snd = inv (pseudoFields {B = B} {D = straighten i .fst})
          ((λ x → x) , (λ x y → Id) , dataOfMap)


    compareGraph : ∀ g → GraphGoal g
    compareGraph g = subst GraphGoal (isContr→isProp graphContr graphCenter g) graphCenterPath

```

Apply the reduction to the given $F$. Global and local univalence turn its action on objects into an equivalence of types, and its action on each hom is already a weak equivalence by hypothesis. This supplies a point of `Graph`, so `compareGraph` recovers the desired path of pairs.

```agda
weakBiequivalence→PointedComparison : ∀ {o h c} {B D : Bicategory o h c}
  (F : Pseudofunctor B D) → isUnivalent B → isUnivalent D → isWeakBiequivalence F → PointedComparison F
weakBiequivalence→PointedComparison {B = B} {D} F uB uD weak =
  Identity.compareGraph B (uB .fst) graph D.structure (fun pseudoFields F .snd .snd) ∙ eta
  where
  module F = Pseudofunctor F
  module D = Bicategory D
  graph : Identity.Graph B (uB .fst)
  graph = (D.Ob , (F.F₀ , isEquivObjectMap F uB uD weak)) , D.hom , λ x y →
    uD .fst _ _ , weakEquivalence (F.Fₕ x y) (weak .fst x y)
  eta : Path (Σ (Bicategory _ _ _) (Pseudofunctor B))
    (pack D.Ob D.hom D.structure , _) (D , F)
  eta i .fst .Bicategory.Ob = D.Ob
  eta i .fst .Bicategory.hom = D.hom
  eta i .fst .Bicategory.structure = D.structure
  eta i .snd = inv (pseudoFields {B = B} {D = eta i .fst}) (fun pseudoFields F)
```

The record path carries the identity pseudofunctor to the specified weak biequivalence. Composing this dependent path with any unit and adjusting its endpoints identifies the two pointed bicategories along that very record path.

```agda
weakBiequivalence→Path : ∀ {o h c} {B D : Bicategory o h c}
  (F : Pseudofunctor B D) → isUnivalent B → isUnivalent D → isWeakBiequivalence F → B ≡ D
weakBiequivalence→Path F u v w = cong fst (weakBiequivalence→PointedComparison F u v w)

weakBiequivalenceUnitPath : ∀ {a b c o h k} {S : Bicategory a b c} {B D : Bicategory o h k}
  (F : Pseudofunctor B D) (u : isUnivalent B) (v : isUnivalent D) (w : isWeakBiequivalence F)
  (η : Pseudofunctor S B) (ι : Pseudofunctor S D) → F ∘P η ≡ ι
  → PathP (λ i → Pseudofunctor S (weakBiequivalence→Path F u v w i)) η ι
weakBiequivalenceUnitPath {S = S} F u v w η ι p =
  subst2 (PathP (λ i → Pseudofunctor S (q i .fst))) (compIdLeft η) p (λ i → q i .snd ∘P η)
  where
  q : PointedComparison F
  q = weakBiequivalence→PointedComparison F u v w
```
