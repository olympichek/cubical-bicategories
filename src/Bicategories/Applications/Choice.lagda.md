# Lifting functors and set choice

Given a weak equivalence $J:B\to E$ and a functor $K:A\to E$ from a strict category, can one lift $K$ to $B$? A lift consists of $H:A\to B$ and an isomorphism $J\circ H\cong K$. When $B$ also has a set of objects, the assertion that such lifts merely exist for every $J,K$ is equivalent to set choice.

```agda
module Bicategories.Applications.Choice where

open import Cubical.Foundations.Prelude hiding (lift)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels hiding (extend)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Instances.Discrete
open import Bicategories.Applications.Presentation
open import Bicategories.PathReasoning

open Category
open Functor
open isWeakEquivalence

```

For a family of sets $Y(s)$ indexed by a set $S$, the principle $\mathrm{AC}_0$ used here has the form

$$
\left(\prod_{s:S}\lVert Y(s)\rVert\right)\;\longrightarrow\;\left\lVert\prod_{s:S}Y(s)\right\rVert.
$$

The outer truncation means that the conclusion is the mere existence of a simultaneous choice.

```agda
SetChoice : (ℓ : Level) → Type (ℓ-suc ℓ)
SetChoice ℓ = (S : hSet ℓ) (Y : fst S → hSet ℓ)
  → ((s : fst S) → ∥ fst (Y s) ∥₁) → ∥ ((s : fst S) → fst (Y s)) ∥₁

isPropSetChoice : ∀ {ℓ} → isProp (SetChoice ℓ)
isPropSetChoice = isPropΠ3 λ _ _ _ → squash₁

module _ {ℓ : Level} {A B E : Category ℓ ℓ}
         (J : Functor B E) (ff : isFullyFaithful J) (K : Functor A E) where
  private
    module B = Category B
    module E = Category E

  Representatives : Type ℓ
  Representatives = (a : ob A) → Σ[ b ∈ ob B ] CatIso E (J ⟅ b ⟆) (K ⟅ a ⟆)

  module LiftFunctor (r : Representatives) where
    private
      obj : ob A → ob B
      obj a = r a .fst

      e : (a : ob A) → CatIso E (J ⟅ obj a ⟆) (K ⟅ a ⟆)
      e a = r a .snd

      arrow : ∀ {x y} → A [ x , y ] → B [ obj x , obj y ]
      arrow {x} {y} f = invEq (_ , ff (obj x) (obj y))
        (e x .fst E.⋆ K ⟪ f ⟫ E.⋆ isIso.inv (e y .snd))

      square : ∀ {x y} (f : A [ x , y ])
        → (J ⟪ arrow f ⟫ E.⋆ e y .fst) ≡ (e x .fst E.⋆ K ⟪ f ⟫)
      square {x} {y} f =
        (J ⟪ arrow f ⟫) E.⋆ e y .fst
          ≡⟨ cong (E._⋆ e y .fst) (secEq (_ , ff (obj x) (obj y)) _) ⟩
        (e x .fst E.⋆ (K ⟪ f ⟫) E.⋆ isIso.inv (e y .snd)) E.⋆ e y .fst
          ≡⟨ E.⋆Assoc _ _ _ ⟩
        e x .fst E.⋆ (((K ⟪ f ⟫) E.⋆ isIso.inv (e y .snd)) E.⋆ e y .fst)
          ≡⟨ cong (e x .fst E.⋆_) cancel ⟩∎
        e x .fst E.⋆ (K ⟪ f ⟫)
        where
        cancel : ((K ⟪ f ⟫) E.⋆ isIso.inv (e y .snd)) E.⋆ e y .fst ≡ K ⟪ f ⟫
        cancel =
          ((K ⟪ f ⟫) E.⋆ isIso.inv (e y .snd)) E.⋆ e y .fst
            ≡⟨ E.⋆Assoc _ _ _ ⟩
          (K ⟪ f ⟫) E.⋆ (isIso.inv (e y .snd) E.⋆ e y .fst)
            ≡[ i ]⟨ (K ⟪ f ⟫) E.⋆ isIso.sec (e y .snd) i ⟩
          (K ⟪ f ⟫) E.⋆ E.id ≡⟨ E.⋆IdR _ ⟩∎ (K ⟪ f ⟫)

      faithful = isFullyFaithful→Faithful {F = J} ff

```

Fix representatives $H(a)$ and isomorphisms $e_a:J(Ha)\cong K(a)$. For $f:a\to b$, full faithfulness gives the unique arrow satisfying $e_b\circ J(Hf)=K(f)\circ e_a$. Use this square twice for a composite to obtain the functor law. The very same squares make the $e_a$ into the comparison natural isomorphism.

```agda
    lift : Functor A B
    lift .F-ob = obj
    lift .F-hom = arrow
    lift .F-id {x} = faithful _ _ _ _ (⋆CancelR (e x)
      ( (J ⟪ arrow (id A) ⟫) E.⋆ e x .fst
          ≡⟨ square (id A) ⟩
        e x .fst E.⋆ (K ⟪ id A ⟫)
          ≡[ i ]⟨ e x .fst E.⋆ K .F-id i ⟩
        e x .fst E.⋆ E.id
          ≡⟨ E.⋆IdR _ ⟩
        e x .fst
          ≡˘⟨ E.⋆IdL _ ⟩
        E.id E.⋆ e x .fst
          ≡⟨ (λ i → J .F-id (~ i) E.⋆ e x .fst) ⟩∎
        (J ⟪ B.id ⟫) E.⋆ e x .fst ))
    lift .F-seq {x} {y} {z} f g = faithful _ _ _ _ (⋆CancelR (e z)
      ( (J ⟪ arrow (f ⋆⟨ A ⟩ g) ⟫) E.⋆ e z .fst
          ≡⟨ square (f ⋆⟨ A ⟩ g) ⟩
        e x .fst E.⋆ (K ⟪ f ⋆⟨ A ⟩ g ⟫)
          ≡[ i ]⟨ e x .fst E.⋆ K .F-seq f g i ⟩
        e x .fst E.⋆ ((K ⟪ f ⟫) E.⋆ (K ⟪ g ⟫))
          ≡˘⟨ E.⋆Assoc _ _ _ ⟩
        (e x .fst E.⋆ (K ⟪ f ⟫)) E.⋆ (K ⟪ g ⟫)
          ≡[ i ]⟨ square f (~ i) E.⋆ (K ⟪ g ⟫) ⟩
        ((J ⟪ arrow f ⟫) E.⋆ e y .fst) E.⋆ (K ⟪ g ⟫)
          ≡⟨ E.⋆Assoc _ _ _ ⟩
        (J ⟪ arrow f ⟫) E.⋆ (e y .fst E.⋆ (K ⟪ g ⟫))
          ≡[ i ]⟨ (J ⟪ arrow f ⟫) E.⋆ square g (~ i) ⟩
        (J ⟪ arrow f ⟫) E.⋆ ((J ⟪ arrow g ⟫) E.⋆ e z .fst)
          ≡˘⟨ E.⋆Assoc _ _ _ ⟩
        ((J ⟪ arrow f ⟫) E.⋆ (J ⟪ arrow g ⟫)) E.⋆ e z .fst
          ≡⟨ (λ i → J .F-seq (arrow f) (arrow g) (~ i) E.⋆ e z .fst) ⟩∎
        (J ⟪ arrow f B.⋆ arrow g ⟫) E.⋆ e z .fst ))

    comparison : NatIso (J ∘F lift) K
    comparison .NatIso.trans .NatTrans.N-ob x = e x .fst
    comparison .NatIso.trans .NatTrans.N-hom = square
    comparison .NatIso.nIso x = e x .snd
```

For each source object $a$, choose from the set of pairs of an object $b$ and an isomorphism from $J(b)$ to $K(a)$. This is a set because the domain of $J$ has a set of objects and isomorphisms between fixed objects form a set. Full faithfulness lifts the arrows after conjugating them by the chosen isomorphisms.

```agda
WeakEquivalenceLifting : (ℓ : Level) → Type (ℓ-suc ℓ)
WeakEquivalenceLifting ℓ =
  (A B E : Category ℓ ℓ) → isSet (ob A) → isSet (ob B)
  → (J : Functor B E) → isWeakEquivalence J → (K : Functor A E)
  → ∥ Σ[ H ∈ Functor A B ] NatIso (J ∘F H) K ∥₁

choice→lifting : ∀ {ℓ} → SetChoice ℓ → WeakEquivalenceLifting ℓ
choice→lifting ac A B E setA setB J w K =
  PT.map (λ r → LiftFunctor.lift J (fullfaith w) K r , LiftFunctor.comparison J (fullfaith w) K r)
    (ac (ob A , setA) (λ a → _ , isSetΣ setB (λ b → isSet-CatIso (J ⟅ b ⟆) (K ⟅ a ⟆)))
      (λ a → esssurj w (K ⟅ a ⟆)))
```

For necessity it suffices to lift the identity along one projection for each family. Over a set $S$ and a set family $Y$, take the groupoid of pairs $(s,y)$ whose arrows are equalities of first coordinates. The projection to the discrete category of $S$ is fully faithful. Pointwise mere inhabitation makes it essentially surjective. A natural isomorphism from the composite to the identity identifies the first coordinate of each chosen pair with its index.

```agda
module Family {ℓ} (S : hSet ℓ) (Y : fst S → hSet ℓ) where
  base = DiscreteCategory (fst S , isSet→isGroupoid (snd S))
  total = Σ[ s ∈ fst S ] fst (Y s)

  projection = inclusion base (fst {B = λ s → fst (Y s)})
  domain = reindex base (fst {B = λ s → fst (Y s)})

  projectionWeak : ((s : fst S) → ∥ fst (Y s) ∥₁) → isWeakEquivalence projection
  projectionWeak inhabited =
    reindexWeakEquivalence base fst λ s → PT.map (λ y → (s , y) , refl) (inhabited s)

  lift→section : (H : Functor base domain) → NatIso (projection ∘F H) (𝟙⟨ base ⟩)
    → (s : fst S) → fst (Y s)
  lift→section H α s =
    subst (λ t → fst (Y t)) (α .NatIso.trans ⟦ s ⟧) ((H ⟅ s ⟆) .snd)

lifting→choice : ∀ {ℓ} → WeakEquivalenceLifting ℓ → SetChoice ℓ
lifting→choice lifts S Y inhabited =
  let open Family S Y in
  PT.map (λ (H , α) → lift→section H α)
    (lifts base domain base (snd S) (isSetΣ (snd S) λ s → snd (Y s))
      projection (projectionWeak inhabited) (𝟙⟨ base ⟩))

lifting≃setChoice : ∀ {ℓ} → WeakEquivalenceLifting ℓ ≃ SetChoice ℓ
lifting≃setChoice = propBiimpl→Equiv
  (isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ →
   isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → squash₁)
  isPropSetChoice lifting→choice choice→lifting
```

## Lifts in completed homs

Fix ordinary completions $R$ with weak units. For a class of categories, local essential surjectivity asks whether every functor between the completions of two strict members is represented by a functor between the original categories. Choice suffices in every class. For the converse the class need only contain the discrete categories of sets and the domains of the family projections.

```agda
open import Bicategories.Categories.RezkCompletion
open import Bicategories.Applications.Categories.Reflection.Base

module Completed {ℓ k} (P : Category ℓ ℓ → Type k)
  (R : (A : Category ℓ ℓ) → RezkCompletion A ℓ ℓ)
  (weak : (A : Category ℓ ℓ) → isWeakEquivalence (unit (R A))) where

  LocalEssentialSurjectivity : Type _
  LocalEssentialSurjectivity =
    (A B : Category ℓ ℓ) → P A → P B → isSet (ob A) → isSet (ob B)
    → (K : Functor (completion (R A)) (completion (R B)))
    → ∥ Σ[ F ∈ Functor A B ] NatIso (reflectFunctor (R A) (R B) F) K ∥₁

  choice→local : SetChoice ℓ → LocalEssentialSurjectivity
  choice→local ac A B _ _ setA setB K =
    PT.map (λ (F , α) → F , pathToNatIso
      ( reflectFunctor (R A) (R B) F
          ≡˘⟨ retEq e _ ⟩
        invEq e (reflectFunctor (R A) (R B) F ∘F unit (R A))
          ≡⟨ cong (invEq e) (reflectFunctorβ (R A) (R B) F ∙ NatIsoToPath u α) ⟩
        invEq e (K ∘F unit (R A))
          ≡⟨ retEq e K ⟩∎
        K ))
      (choice→lifting ac A B (completion (R B)) setA setB
        (unit (R B)) (weak B) (K ∘F unit (R A)))
    where
    u = univalent (R B)
    e = restrictFunctors (R A) u

```

For necessity, specialize the completed-hom lifting hypothesis to a family projection. Extend the projection to completions, lift the relevant diagram on the base, then restrict the comparison back to original objects. The resulting section picks an element in each fiber, under the truncation required by set choice.

```agda
  module Converse
    (discrete : (S : hSet ℓ) → P (DiscreteCategory (fst S , isSet→isGroupoid (snd S))))
    (family : (S : hSet ℓ) (Y : fst S → hSet ℓ) → P (Family.domain S Y)) where

    local→choice : LocalEssentialSurjectivity → SetChoice ℓ
    local→choice lifts S Y inhabited = PT.map extract
      (lifts base domain (discrete S) (family S Y) (snd S)
        (isSetΣ (snd S) λ s → snd (Y s)) K)
      where
      open Family S Y

      uBase : isUnivalent base
      uBase .isUnivalent.univ x y =
        propBiimpl→isEquiv (snd S x y)
          (λ f g → CatIso≡ f g (snd S x y _ _)) fst

      rB = R domain
      rA = R base
      q = fromWeakUnit projection uBase (projectionWeak inhabited)

      H = extend q (univalent rB) (unit rB)
      K = extend rA (univalent rB) H
      pr = extend rB uBase projection

      prH : pr ∘F H ≡ Id
      prH =
        pr ∘F H
          ≡˘⟨ retEq e (pr ∘F H) ⟩
        invEq e ((pr ∘F H) ∘F projection)
          ≡[ i ]⟨ invEq e (atProjection i) ⟩
        invEq e (Id ∘F projection)
          ≡⟨ retEq e Id ⟩∎
        Id
        where
        e = restrictFunctors q uBase
        atProjection : (pr ∘F H) ∘F projection ≡ Id ∘F projection
        atProjection =
          (pr ∘F H) ∘F projection
            ≡˘⟨ F-assoc ⟩
          pr ∘F (H ∘F projection)
            ≡[ i ]⟨ pr ∘F extendβ q (univalent rB) (unit rB) i ⟩
          pr ∘F unit rB
            ≡⟨ extendβ rB uBase projection ⟩
          projection ≡⟨ sym F-rUnit ⟩∎ Id ∘F projection

      extract : Σ[ F ∈ Functor base domain ] NatIso (reflectFunctor rA rB F) K
        → (s : fst S) → fst (Y s)
      extract (F , α) = lift→section F (pathToNatIso
        ( projection ∘F F
            ≡[ i ]⟨ extendβ rB uBase projection (~ i) ∘F F ⟩
          (pr ∘F unit rB) ∘F F
            ≡˘⟨ F-assoc ⟩
          pr ∘F (unit rB ∘F F)
            ≡[ i ]⟨ pr ∘F atUnit i ⟩
          pr ∘F H ≡⟨ prH ⟩∎ Id ))
        where
        atUnit : unit rB ∘F F ≡ H
        atUnit =
          unit rB ∘F F
            ≡˘⟨ reflectFunctorβ rA rB F ⟩
          reflectFunctor rA rB F ∘F unit rA
            ≡[ i ]⟨ NatIsoToPath (univalent rB) α i ∘F unit rA ⟩
          K ∘F unit rA ≡⟨ extendβ rA (univalent rB) H ⟩∎ H

    localEssentialSurjectivity≃setChoice : LocalEssentialSurjectivity ≃ SetChoice ℓ
    localEssentialSurjectivity≃setChoice = propBiimpl→Equiv
      (isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ →
       isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → squash₁)
      isPropSetChoice local→choice choice→local
```
