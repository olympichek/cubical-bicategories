# An intrinsic obstruction to biequivalence

Can a weak biequivalence $J$ from all small categories to univalent categories exist? Consider the one-object groupoid $G$ of order two and its ordinary completion unit $i:G\to R$. The proof derives from any such $J$ a functor $v:R\to G$ with $i\circ v\cong 1_R$. The nonidentity automorphism of $G$ obstructs precisely this lift.

```agda
module Bicategories.Applications.Categories.Obstruction where

open import Cubical.Foundations.Prelude hiding (_▷_; _◁_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥; isProp⊥)
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functor.Compose
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Isomorphism
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties using (compPseudofunctor)
open import Bicategories.Equivalence
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.WeakBiequivalence.Properties using (isWeakBiequivalenceComp)
open import Bicategories.Instances.Categories
open import Bicategories.Smallness.Lift using (module LevelLift)
import Bicategories.Categories.RezkCompletion as RC
open import Bicategories.Categories.Instances.RezkByHIT
open import Bicategories.Categories.WeakEquivalence using (weakComposite)
open import Bicategories.Examples.TerminalComparison
  using (Terminal; terminalUnivalent; TwoGroup; identityDoesNotLift)
open import Bicategories.Applications.Categories.Obstruction.Points
open Functor
open Category
open NatIso
open NatTrans
open isWeakEquivalence

private
  module _ {o h r s d e} {A : Category o h} {B : Category r s} {D : Category d e}
    (F : Functor A B) (G : Functor B D) (u : isUnivalent B) where

    cancelWeakRight : isWeakEquivalence F → isWeakEquivalence (G ∘F F) → isWeakEquivalence G
    cancelWeakRight v w .esssurj d = PT.map (λ (a , p) → F ⟅ a ⟆ , p) (w .esssurj d)
    cancelWeakRight v w .fullfaith b b′ = PT.rec2 (isPropIsEquiv _) atRepresentatives (onto b) (onto b′)
      where
      onto = isSurj→isSurj-ob u {F = F} (v .esssurj)
      goal = λ x y → isEquiv (G .F-hom {x} {y})
      atRepresentatives : fiber (F .F-ob) b → fiber (F .F-ob) b′ → goal b b′
      atRepresentatives (a , p) (a′ , q) = subst2 goal p q
        (rCancelIsEquiv (G .F-hom) (F .F-hom) (w .fullfaith a a′) (v .fullfaith a a′))

  module _ {a b c d e f} {S : Bicategory a b c} {D : Bicategory d e f}
    (J : Pseudofunctor S D) where
    private
      module S = Bicategory S
      module D = Bicategory D
      module J = Pseudofunctor J

    whiskerComparison : (t x y : S.Ob) (i : S.Cell x y)
      → NatIso (D.rightWhisker (J.F₁ i) ∘F J.Fₕ t x)
               (J.Fₕ t y ∘F S.rightWhisker i)
    whiskerComparison t x y i .trans .N-ob f = J.compositor f i .fst
    whiskerComparison t x y i .trans .N-hom {_} {g} θ =
      cong (λ v → (J.F₂ θ D.⊗ v) D.⋆₂ J.compositor g i .fst)
        (sym (J.Fₕ x y .F-id))
      ∙ J.compositor-natural θ (S.id₂ i)
    whiskerComparison t x y i .nIso f = J.compositor f i .snd
```

Let $T$ be the terminal category and let $i:G\to R$ be the completion unit. Postcomposition by $i$ on diagrams of shape $T$ is weak. The compositor of $J$ intertwines it with postcomposition by $J(i)$ on diagrams of shape $J(T)$. Both vertical hom functors are weak. Local univalence converts the natural isomorphism of composites to a path and lets us cancel the first vertical functor.

```agda
private
  module Detect {ℓ k} (J : Pseudofunctor (CAT ℓ) (UNIVCAT k)) (weak : isWeakBiequivalence J) where
    module J = Pseudofunctor J
    S = CAT ℓ
    D = UNIVCAT k
    module G = LevelLift TwoGroup ℓ ℓ
    T = LevelLift.category Terminal ℓ ℓ
    R = RC.completion (smallCompletion G.category)
    i = RC.unit (smallCompletion G.category)
    wi = isWeakEquivalenceUnit G.category
    Ji = J.F₁ {G.category} {R} i

    image : Category ℓ ℓ → Category k k
    image C = J.F₀ C .fst

    private
      top = Bicategory.rightWhisker S {T} {G.category} {R} i
      bottom = Bicategory.rightWhisker D {J.F₀ T} {J.F₀ G.category} {J.F₀ R} Ji

      topWeak : isWeakEquivalence top
      topWeak = subst isWeakEquivalence (sym (catWhiskerPath T G.category R i))
        (terminalPostWeak ℓ i wi)

      square : bottom ∘F J.Fₕ T G.category ≡ J.Fₕ T R ∘F top
      square = invEq (Path≃NatIso (isLocallyUnivalentUNIVCAT (J.F₀ T) (J.F₀ R)))
        (whiskerComparison J T G.category R i)

      bottomWeak : isWeakEquivalence bottom
      bottomWeak = cancelWeakRight (J.Fₕ T G.category) bottom
        (isLocallyUnivalentUNIVCAT (J.F₀ T) (J.F₀ G.category))
        (weak .fst T G.category)
        (subst isWeakEquivalence (sym square)
          (weakComposite {F = top} {G = J.Fₕ T R} topWeak (weak .fst T R)))

    postWeak : isWeakEquivalence (postcomposeF (image T) Ji)
    postWeak = subst isWeakEquivalence
      (catWhiskerPath (image T) (image G.category) (image R) Ji) bottomWeak
```

The category $J(T)$ is merely inhabited. Indeed some $J(Y)$ is adjoint equivalent to a terminal category, and the image of the functor $Y\to T$ sends its point to $J(T)$. Testing constant diagrams at that point shows $J(i)$ is weak. Its source and target are univalent, so it has a mere inverse functor. Lift this inverse through the weak hom functor and its counit through full faithfulness.

```agda
    inhabited : ∥ ob (image T) ∥₁
    inhabited = PT.map point (weak .snd target)
      where
      module Term = LevelLift Terminal k k
      target = Term.category , Term.univalent terminalUnivalent
      point : Σ[ Y ∈ Category ℓ ℓ ] AdjointEquivalence D (J.F₀ Y) target → ob (image T)
      point (Y , f , a) = J.F₁ (Constant Y T (lift tt)) ⟅ a .AdjointStructure.inverse ⟅ lift tt ⟆ ⟆

```

For a point of $J(T)$, evaluating constant diagrams at that point detects weakness of $J(i)$. Weakness is a proposition, so mere inhabitation suffices. Between univalent categories this weak equivalence has a merely existing inverse functor.

```agda
    inverseImage : isEquivalence Ji
    inverseImage = PT.rec squash₁ (λ t → isWeakEquiv→isEquiv
      (J.F₀ G.category .snd) (J.F₀ R .snd) {F = Ji}
      (postcomposeReflectsWeak (image T) Ji t postWeak)) inhabited

    noLift : ∥ Σ[ U ∈ Functor R G.category ] NatIso (i ∘F U) Id ∥₁ → ⊥
    noLift lift₁ = identityDoesNotLift (RC.univalent (smallCompletion G.category)) (i ∘F G.up)
      (isFullyFaithfulG∘F {F = G.up} {G = i} (λ _ _ → LiftEquiv .snd) (wi .fullfaith))
      (PT.map shrink lift₁)
      where
      shrink : Σ[ U ∈ Functor R G.category ] NatIso (i ∘F U) Id
        → Σ[ U ∈ Functor R TwoGroup ] NatIso ((i ∘F G.up) ∘F U) Id
      shrink (U , n) = G.down ∘F U , subst (λ K → NatIso K Id) (Functor≡ (λ _ → refl) (λ _ → refl)) n

```

Apply essential surjectivity on the hom-category from $R$ to $G$ to lift an inverse for $J(i)$ to a candidate $v:R\to G$. Full faithfulness on the hom from $R$ to itself lifts the counit isomorphism to $i\circ v\cong 1_R$. This is the witness excluded by `noLift`.

```agda
    contradiction : ⊥
    contradiction = PT.rec isProp⊥ fromInverse inverseImage
      where
      fromInverse : WeakInverse Ji → ⊥
      fromInverse v = noLift (PT.map recover (weak .fst R G.category .esssurj (v .WeakInverse.invFunc)))
        where
        recover : Σ[ U ∈ Functor R G.category ]
            CatIso (FUNCTOR (image R) (image G.category)) (J.F₁ U) (v .WeakInverse.invFunc)
          → Σ[ U ∈ Functor R G.category ] NatIso (i ∘F U) Id
        recover (U , e) = U , FUNCTORIso→NatIso R R
          (liftIso {F = J.Fₕ R R} (weak .fst R R .fullfaith)
            (⋆Iso (invIso (J.compositor U i))
            (⋆Iso (F-Iso {F = postcomposeF (image R) Ji} e)
            (⋆Iso (NatIso→FUNCTORIso _ _ (v .WeakInverse.ε)) (J.unit R)))))

```

This contradiction applies to every candidate $J$. Composing a hypothetical weak biequivalence from the bicategorical Rezk completion of categories with its weak unit would give one from categories themselves, so the obstruction also rules out that composite.

```agda
noWeakCAT→UNIVCAT : ∀ {ℓ k} (J : Pseudofunctor (CAT ℓ) (UNIVCAT k))
  → isWeakBiequivalence J → ⊥
noWeakCAT→UNIVCAT = Detect.contradiction

noWeakCompletion→UNIVCAT : ∀ {ℓ k o h c} {B : Bicategory o h c}
  (η : Pseudofunctor (CAT ℓ) B) → isWeakBiequivalence η
  → (F : Pseudofunctor B (UNIVCAT k)) → isWeakBiequivalence F → ⊥
noWeakCompletion→UNIVCAT η w F v =
  noWeakCAT→UNIVCAT (compPseudofunctor F η) (isWeakBiequivalenceComp F η v w)
```

At matching levels the structure identity principle also excludes weak biequivalences directed from univalent categories to the completion. Such a map would identify the two bicategory records, and transporting the original weak unit across this identification would contradict the obstruction.

```agda
open import Bicategories.StructureIdentity using (weakBiequivalence→Path)
import Bicategories.Univalence as Bi

module _ {ℓ k} {R : Bicategory (ℓ-suc k) k k}
  (η : Pseudofunctor (CAT ℓ) R) (weak : isWeakBiequivalence η) where

  completion≢UNIVCAT : R ≡ UNIVCAT k → ⊥
  completion≢UNIVCAT p = subst
    (λ U → (J : Pseudofunctor (CAT ℓ) U) → isWeakBiequivalence J → ⊥)
    (sym p) noWeakCAT→UNIVCAT η weak

  noWeakUNIVCAT→Completion : Bi.isUnivalent R
    → (F : Pseudofunctor (UNIVCAT k) R) → isWeakBiequivalence F → ⊥
  noWeakUNIVCAT→Completion u F w = completion≢UNIVCAT
    (sym (weakBiequivalence→Path F isUnivalentUNIVCAT u w))
```
