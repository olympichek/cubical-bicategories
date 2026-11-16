# The ordinary completion pseudofunctor

For a family of ordinary completions $\eta_A:A\to QA$, extension sends $F:A\to B$ to a functor $QF:QA\to QB$. To make this action a pseudofunctor we must also lift natural transformations and compare lifts of composites.

```agda
module Bicategories.Applications.Categories.CompletionFunctor where

open import Cubical.Foundations.Prelude hiding (comp; lift)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels hiding (extend)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism using (compSq)
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Functor.ComposeProperty
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Instances.Functors
open import Bicategories.Categories.RezkCompletion as RC
open import Bicategories.Applications.Categories.Reflection.Base
open import Bicategories.Instances.Categories
open import Bicategories.Base using (Bicategory)
open import Bicategories.Pseudofunctor.Base using (Pseudofunctor)
open import Bicategories.Pseudofunctor.Properties using (idPseudofunctor)

open Category
open Functor
open NatTrans

module Construction {ℓ i} {X : Type i} (cat : X → Category ℓ ℓ)
  (R : (A : X) → RezkCompletion (cat A) ℓ ℓ) where
  private
    variable
      A B C D : X
    Q : X → Category ℓ ℓ
    Q A = completion (R A)
    η : (A : X) → Functor (cat A) (Q A)
    η A = unit (R A)

```

A representative of $b$ in $QA$ is an original object $a$ with an isomorphism $u:\eta_A(a)\cong b$. Given another representative $v:\eta_A(a^{\prime})\cong b^{\prime}$, `Over` says that arrows $f:a\to a^{\prime}$ and $k:b\to b^{\prime}$ form a commuting square with $u,v$. These squares compose.

```agda
  Representative : (A : X) → ob (cat A) → ob (Q A) → Type ℓ
  Representative A a b = CatIso (Q A) (η A ⟅ a ⟆) b

  Over : {A : X} {a a' : ob (cat A)} {b b' : ob (Q A)}
    → Representative A a b → Representative A a' b' → cat A [ a , a' ] → Q A [ b , b' ]
    → Type ℓ
  Over {A} u v f k = (η A ⟪ f ⟫ ⋆⟨ Q A ⟩ v .fst) ≡ (u .fst ⋆⟨ Q A ⟩ k)

  overId : {A : X} {a : ob (cat A)} {b : ob (Q A)} (u : Representative A a b)
    → Over {A} u u (id (cat A)) (id (Q A))
  overId {A} u = cong (λ h → h ⋆⟨ Q A ⟩ u .fst) (η A .F-id)
    ∙ ⋆IdL (Q A) _ ∙ sym (⋆IdR (Q A) _)

  overSeq : {A : X} {a a' a'' : ob (cat A)} {b b' b'' : ob (Q A)}
    {u : Representative A a b} {v : Representative A a' b'} {w : Representative A a'' b''}
    {f : cat A [ a , a' ]} {g : cat A [ a' , a'' ]} {k : Q A [ b , b' ]} {l : Q A [ b' , b'' ]}
    → Over {A} u v f k → Over {A} v w g l → Over {A} u w (f ⋆⟨ cat A ⟩ g) (k ⋆⟨ Q A ⟩ l)
  overSeq {A} {w = w} {f} {g} p q =
    cong (λ h → h ⋆⟨ Q A ⟩ w .fst) (η A .F-seq f g)
    ∙ sym (compSq (Q A) (sym p) (sym q))

```

Pair $F:A\to B$ with a functor $K:QA\to QB$. An `Action` sends a representative $u$ to one for $K(b)$ by $F(a)$ and sends squares to squares. The extension rule gives this action for $K=QF$ by composing the comparison at $a$ with $K(u)$.

```agda
  record Action {A B : X} (F : Functor (cat A) (cat B)) (K : Functor (Q A) (Q B))
                : Type ℓ where
    field
      image : {a : ob (cat A)} {b : ob (Q A)}
        → Representative A a b → Representative B (F ⟅ a ⟆) (K ⟅ b ⟆)
      square : {a a' : ob (cat A)} {b b' : ob (Q A)}
        {u : Representative A a b} {v : Representative A a' b'}
        {f : cat A [ a , a' ]} {k : Q A [ b , b' ]}
        → Over {A} u v f k → Over {B} (image u) (image v) (F ⟪ f ⟫) (K ⟪ k ⟫)

  open Action

  identity : Action {A} {A} Id Id
  identity .image u = u
  identity .square p = p

  composite : {F : Functor (cat A) (cat B)} {G : Functor (cat B) (cat C)}
    {K : Functor (Q A) (Q B)} {L : Functor (Q B) (Q C)}
    → Action {A} {B} F K → Action {B} {C} G L → Action {A} {C} (G ∘F F) (L ∘F K)
  composite f g .image u = g .image (f .image u)
  composite f g .square p = g .square (f .square p)

  lift₁ : (F : Functor (cat A) (cat B)) → Functor (Q A) (Q B)
  lift₁ {A = A} {B = B} = reflectFunctor (R A) (R B)

  opaque
    action : (F : Functor (cat A) (cat B)) → Action {A} {B} F (lift₁ {A = A} {B} F)
    action {A = A} {B = B} F = out
      where
      K : Functor (Q A) (Q B)
      K = lift₁ {A = A} {B} F
      β : NatIso (η B ∘F F) (K ∘F η A)
      β = pathToNatIso (sym (reflectFunctorβ (R A) (R B) F))

      out : Action {A} {B} F K
      out .image {a} u = ⋆Iso (_ , β .NatIso.nIso a) (F-Iso {F = K} u)
      out .square {u = u} {v} {f} {k} p = compSq (Q B) (β .NatIso.trans .N-hom f)
        (sym (K .F-seq _ _) ∙ cong (F-hom K) p ∙ K .F-seq _ _)
```

A lifted transformation is determined by its components at objects in the image of the source unit. At such an object its component is conjugation by the two representative isomorphisms. Naturality then gives the same square at every represented object and for every choice of representing isomorphism.

```agda
  module _ {A B} {F : Functor (cat A) (cat B)} {K : Functor (Q A) (Q B)}
           (f : Action {A} {B} F K) where

    comparison : NatIso (η B ∘F F) (K ∘F η A)
    comparison .NatIso.trans .N-ob x = f .image (idCatIso {x = η A ⟅ x ⟆}) .fst
    comparison .NatIso.trans .N-hom a = f .square
      (⋆IdR (Q A) (η A ⟪ a ⟫) ∙ sym (⋆IdL (Q A) _))
    comparison .NatIso.nIso x = f .image idCatIso .snd

    slide : {x : ob (cat A)} {y : ob (Q A)} (u : Representative A x y)
      → (comparison .NatIso.trans ⟦ x ⟧ ⋆⟨ Q B ⟩ K ⟪ u .fst ⟫) ≡ f .image u .fst
    slide {x} u = sym (f .square {u = idCatIso} {v = u} {f = id (cat A)}
      (cong (λ a → a ⋆⟨ Q A ⟩ u .fst) (η A .F-id)))
      ∙ cong (λ a → a ⋆⟨ Q B ⟩ f .image u .fst)
        (cong (F-hom (η B)) (F .F-id) ∙ η B .F-id)
      ∙ ⋆IdL (Q B) _

  module Cells {A B} {F G : Functor (cat A) (cat B)} {K L : Functor (Q A) (Q B)}
    (f : Action {A} {B} F K) (g : Action {A} {B} G L) where
    private
      module E = Category (Q B)
      e = comparison f
      d = comparison g

    Compatible : NatTrans F G → NatTrans K L → Type ℓ
    Compatible α β = {x : ob (cat A)} {y : ob (Q A)} (u : Representative A x y)
      → Over {B} (f .image u) (g .image u) (α ⟦ x ⟧) (β ⟦ y ⟧)

    unique : {α α' : NatTrans F G} {β β' : NatTrans K L}
      → Compatible α β → Compatible α' β' → α ≡ α' → β ≡ β'
    unique p q t = isFullyFaithful→Faithful
      {F = precomposeF (Q B) (η A)}
      (λ _ _ → restrictNatural (R A) (univalent (R B)) _ _ .snd)
      _ _ _ _ (makeNatTransPath (funExt λ x → ⋆CancelL (f .image (idCatIso {x = η A ⟅ x ⟆}))
        (sym (p idCatIso) ∙ cong (λ α → η B ⟪ α ⟦ x ⟧ ⟫ E.⋆ _) t ∙ q idCatIso)))

    private
      atUnit : (α : NatTrans F G) → NatTrans (K ∘F η A) (L ∘F η A)
      atUnit α = ((symNatIso e .NatIso.trans) ●ᵛ (η B ∘ʳ α)) ●ᵛ d .NatIso.trans

    opaque
      liftCell : NatTrans F G → NatTrans K L
      liftCell α = invEq (restrictNatural (R A) (univalent (R B)) K L) (atUnit α)

      liftCellβ : (α : NatTrans F G)
        → invEq (restrictNatural (R A) (univalent (R B)) K L) (atUnit α) ≡ liftCell α
      liftCellβ α = refl

      preserves : (α : NatTrans F G) → Compatible α (liftCell α)
      preserves α {x} {y} u =
          cong (η B ⟪ α ⟦ x ⟧ ⟫ E.⋆_) (sym (slide g u)) ∙ sym (E.⋆Assoc _ _ _)
        ∙ cong (E._⋆ L ⟪ u .fst ⟫) canonical ∙ E.⋆Assoc _ _ _
        ∙ cong (e .NatIso.trans ⟦ x ⟧ E.⋆_) (sym (liftCell α .N-hom (u .fst)))
        ∙ sym (E.⋆Assoc _ _ _) ∙ cong (E._⋆ liftCell α ⟦ y ⟧) (slide f u)
        where
        canonical : (η B ⟪ α ⟦ x ⟧ ⟫ E.⋆ d .NatIso.trans ⟦ x ⟧)
                  ≡ (e .NatIso.trans ⟦ x ⟧ E.⋆ liftCell α ⟦ η A ⟅ x ⟆ ⟧)
        canonical = sym (cong (e .NatIso.trans ⟦ x ⟧ E.⋆_)
          (cong (_⟦ x ⟧) (secEq (restrictNatural (R A) (univalent (R B)) K L) (atUnit α)))
          ∙ sym (E.⋆Assoc _ _ _) ∙ cong (E._⋆ d .NatIso.trans ⟦ x ⟧) (sym (E.⋆Assoc _ _ _)
            ∙ cong (E._⋆ η B ⟪ α ⟦ x ⟧ ⟫) (e .NatIso.nIso x .isIso.ret) ∙ E.⋆IdL _))

      liftInvertible : (α : CatIso (FUNCTOR (cat A) (cat B)) F G)
        → isIso (FUNCTOR (Q A) (Q B)) (liftCell (α .fst))
      liftInvertible α = isFullyFaithful→Conservative
        {F = precomposeF (Q B) (η A)}
        (λ _ _ → restrictNatural (R A) (univalent (R B)) _ _ .snd)
        (subst (isIso (FUNCTOR (cat A) (Q B)))
          (sym (secEq (restrictNatural (R A) (univalent (R B)) K L) (atUnit (α .fst))))
          (NatIso→FUNCTORIso _ _ (seqNatIso
            (seqNatIso (symNatIso e) (η B ∘ʳi FUNCTORIso→NatIso _ _ α)) d) .snd))
```

## Coherence by uniqueness

Pair each functor with its lift and the action on representatives. Parallel pairs admit cells whenever their original and lifted transformations form compatible squares. Horizontal and vertical composition are pasting of squares. Thus the two sides of a coherence law have equal lifts as soon as their original transformations agree.

```agda
  private
    record Arrow (A B : X) : Type ℓ where
      constructor arrow
      field
        src : Functor (cat A) (cat B)
        dst : Functor (Q A) (Q B)
        acts : Action {A} {B} src dst
    open Arrow

    ident : Arrow A A
    ident {A} = arrow Id Id (identity {A = A})

    inn : (F : Functor (cat A) (cat B)) → Arrow A B
    inn {A} {B} F = arrow F (lift₁ {A = A} {B} F) (action {A = A} {B} F)

    _then_ : Arrow A B → Arrow B C → Arrow A C
    f then g = arrow (g .src ∘F f .src) (g .dst ∘F f .dst) (composite (f .acts) (g .acts))

    record Cell {A B : X} (f g : Arrow A B) : Type ℓ where
      constructor cell
      field
        original : NatTrans (f .src) (g .src)
        lifted : NatTrans (f .dst) (g .dst)
        respects : Cells.Compatible (f .acts) (g .acts) original lifted
    open Cell

    same : {f g : Arrow A B} (p q : Cell f g) → p .original ≡ q .original → p .lifted ≡ q .lifted
    same {f = f} {g} p q =
      Cells.unique (f .acts) (g .acts) (p .respects) (q .respects)

    chosen : (f g : Arrow A B) → NatTrans (f .src) (g .src) → Cell f g
    chosen f g α = cell α (Cells.liftCell (f .acts) (g .acts) α)
      (Cells.preserves (f .acts) (g .acts) α)

    isom : (f g : Arrow A B) (α : CatIso (FUNCTOR (cat A) (cat B)) (f .src) (g .src))
      → CatIso (FUNCTOR (Q A) (Q B)) (f .dst) (g .dst)
    isom f g α = chosen f g (α .fst) .lifted , Cells.liftInvertible (f .acts) (g .acts) α

    reflCell : (f : Arrow A B) → Cell f f
    reflCell {B = B} f = cell (idTrans _) (idTrans _) λ u → overId {A = B} (f .acts .image u)

    seq : {f g h : Arrow A B} → Cell f g → Cell g h → Cell f h
    seq {B = B} {f} {g} {h} p q = cell (seqTrans (p .original) (q .original))
      (seqTrans (p .lifted) (q .lifted)) λ u → overSeq {A = B}
        {u = f .acts .image u} {v = g .acts .image u} {w = h .acts .image u}
        (p .respects u) (q .respects u)

    horiz : {f f' : Arrow A B} {g g' : Arrow B C}
      → Cell f f' → Cell g g' → Cell (f then g) (f' then g')
    horiz {C = C} {f} {f'} {g} {g'} p q = cell (whiskerTrans (q .original) (p .original))
      (whiskerTrans (q .lifted) (p .lifted)) λ u →
        overSeq {A = C} {u = g .acts .image (f .acts .image u)}
          {v = g .acts .image (f' .acts .image u)} {w = g' .acts .image (f' .acts .image u)}
          (g .acts .square (p .respects u)) (q .respects (f' .acts .image u))

    module S = Bicategory (CAT ℓ)
    module IdMap = Pseudofunctor (idPseudofunctor (CAT ℓ))

    left : (f : Arrow A B) → Cell (ident then f) f
    left {B = B} f = cell (S.leftUnitor (f .src) .fst) (S.leftUnitor (f .dst) .fst)
      (λ u → overId {A = B} (f .acts .image u))

    right : (f : Arrow A B) → Cell (f then ident) f
    right {B = B} f = cell (S.rightUnitor (f .src) .fst) (S.rightUnitor (f .dst) .fst)
      (λ u → overId {A = B} (f .acts .image u))

    assoc : (f : Arrow A B) (g : Arrow B C) (h : Arrow C D)
      → Cell ((f then g) then h) (f then (g then h))
    assoc {D = D} f g h = cell (S.associator (f .src) (g .src) (h .src) .fst)
      (S.associator (f .dst) (g .dst) (h .dst) .fst)
      (λ u → overId {A = D} (h .acts .image (g .acts .image (f .acts .image u))))

    ηcell : (a : X) → Cell (ident {A = a}) (inn Id)
    ηcell a = chosen ident (inn Id) (idTrans _)

    μcell : (f : Functor (cat A) (cat B)) (g : Functor (cat B) (cat C))
      → Cell (inn {A = A} {B} f then inn {A = B} {C} g) (inn (g ∘F f))
    μcell f g = chosen _ _ (idTrans _)

  open import Bicategories.FullSubbicategory using (reindex)

```

On a hom-category, `mapHoms` sends $F$ to its extension and a natural transformation to its compatible lift. For the pseudofunctor laws, each use of `same` reduces equality of two lifted transformations to the corresponding equality before completion.

```agda
  mapHoms : (a b : X) → Functor (FUNCTOR (cat a) (cat b)) (FUNCTOR (Q a) (Q b))
  mapHoms a b .F-ob = lift₁ {A = a} {b}
  mapHoms a b .F-hom {F} {G} α = chosen (inn {A = a} {b} F) (inn G) α .lifted
  mapHoms a b .F-id {F} = same (chosen _ _ (idTrans F)) (reflCell (inn {A = a} {b} F)) refl
  mapHoms a b .F-seq {F} {G} {H} α β = same
    (chosen (inn {A = a} {b} F) (inn H) (seqTrans α β))
    (seq (chosen _ (inn G) α) (chosen (inn G) _ β)) refl

  reflection : Pseudofunctor (reindex (CAT ℓ) cat) (reindex (CAT ℓ) Q)
  reflection .Pseudofunctor.F₀ a = a
  reflection .Pseudofunctor.Fₕ = mapHoms
  reflection .Pseudofunctor.unit a = isom (ident {A = a}) (inn Id) idCatIso
  reflection .Pseudofunctor.compositor {a} {b} {c} f g =
    isom (inn {A = a} {b} f then inn {A = b} {c} g) (inn (g ∘F f)) idCatIso
  reflection .Pseudofunctor.compositor-natural {a} {b} {c} {f} {f'} {g} {g'} α β =
    same {f = F f then G g} {H (g' ∘F f')}
      (seq (horiz (chosen (F f) (F f') α) (chosen (G g) (G g') β))
           (μcell {A = a} {b} {c} f' g'))
      (seq (μcell {A = a} {b} {c} f g) (chosen (H (g ∘F f)) (H (g' ∘F f')) (whiskerTrans β α)))
      (IdMap.compositor-natural {x = cat a} {cat b} {cat c} {f} {f'} {g} {g'} α β)
    where
    F = inn {A = a} {b}
    G = inn {A = b} {c}
    H = inn {A = a} {c}
  reflection .Pseudofunctor.leftUnitor-law {x = a} {b} f =
    same {f = ident then F f} {F f}
      (seq (seq (horiz (ηcell a) (reflCell (F f))) (μcell {A = a} {a} {b} Id f))
           (chosen (F (f ∘F Id)) (F f) (S.leftUnitor f .fst)))
      (left (F f)) (IdMap.leftUnitor-law {x = cat a} {cat b} f)
    where F = inn {A = a} {b}
  reflection .Pseudofunctor.rightUnitor-law {x = a} {b} f =
    same {f = F f then ident} {F f}
      (seq (seq (horiz (reflCell (F f)) (ηcell b)) (μcell {A = a} {b} {b} f Id))
           (chosen (F (Id ∘F f)) (F f) (S.rightUnitor f .fst)))
      (right (F f)) (IdMap.rightUnitor-law {x = cat a} {cat b} f)
    where F = inn {A = a} {b}
  reflection .Pseudofunctor.associator-law {w = a} {b} {c} {d} f g h =
    same {f = ((F f then G g) then H h)} {inn ((h ∘F g) ∘F f)}
      (seq (seq (horiz (μcell {A = a} {b} {c} f g) (reflCell (H h)))
                (μcell {A = a} {c} {d} (g ∘F f) h))
           (chosen (inn {A = a} {d} (h ∘F (g ∘F f))) (inn ((h ∘F g) ∘F f))
             (S.associator f g h .fst)))
      (seq (seq (assoc (F f) (G g) (H h))
                (horiz (reflCell (F f)) (μcell {A = b} {c} {d} g h)))
           (μcell {A = a} {b} {d} f (h ∘F g)))
      (IdMap.associator-law {w = cat a} {cat b} {cat c} {cat d} f g h)
    where
    F = inn {A = a} {b}
    G = inn {A = b} {c}
    H = inn {A = c} {d}
```

Restriction on natural transformations is an equivalence. At represented objects the lifted transformation is obtained by postcomposition with the target unit followed by conjugation with two isomorphisms. Consequently a fully faithful target unit makes the reflection fully faithful on parallel 2-cells.

```agda
  private
    open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv)

    preIso : (E : Category ℓ ℓ) {x y z : ob E} (u : CatIso E x y)
      → E [ y , z ] ≃ E [ x , z ]
    preIso E u = isoToEquiv (iso (_⋆_ E (fst u)) (_⋆_ E (isIso.inv (snd u)))
      (λ f → sym (⋆Assoc E _ _ _) ∙ cong (λ h → h ⋆⟨ E ⟩ f) (isIso.ret (snd u)) ∙ ⋆IdL E _)
      (λ f → sym (⋆Assoc E _ _ _) ∙ cong (λ h → h ⋆⟨ E ⟩ f) (isIso.sec (snd u)) ∙ ⋆IdL E _))

    postIso : (E : Category ℓ ℓ) {x y z : ob E} (u : CatIso E y z)
      → E [ x , y ] ≃ E [ x , z ]
    postIso E u = isoToEquiv (iso (λ h → h ⋆⟨ E ⟩ fst u) (λ h → h ⋆⟨ E ⟩ isIso.inv (snd u))
      (λ f → ⋆Assoc E _ _ _ ∙ cong (_⋆_ E f) (isIso.sec (snd u)) ∙ ⋆IdR E _)
      (λ f → ⋆Assoc E _ _ _ ∙ cong (_⋆_ E f) (isIso.ret (snd u)) ∙ ⋆IdR E _))

  isFullyFaithfulMapHoms : (a b : X) → isFullyFaithful (η b) → isFullyFaithful (mapHoms a b)
  isFullyFaithfulMapHoms a b ff f g =
    subst isEquiv (funExt λ α → cong (invEq restriction) (makeNatTransPath refl)
      ∙ Cells.liftCellβ (action {A = a} {b} f) (action {A = a} {b} g) α)
    ((post ∙ₑ preIso T (NatIso→FUNCTORIso _ _ (symNatIso e)) ∙ₑ
      postIso T (NatIso→FUNCTORIso _ _ d) ∙ₑ
      invEquiv restriction) .snd)
    where
    restriction = restrictNatural (R a) (univalent (R b)) (lift₁ {A = a} {b} f) (lift₁ {A = a} {b} g)
    T = FUNCTOR (cat a) (Q b)
    e = comparison (action {A = a} {b} f)
    d = comparison (action {A = a} {b} g)
    post = _ , isFullyFaithfulPostcomposeF {C = cat a} {G = η b} ff f g
```
