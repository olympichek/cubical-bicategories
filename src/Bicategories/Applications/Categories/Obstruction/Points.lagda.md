# Testing a functor on categories of diagrams

To detect whether a functor $F:A\to B$ is a weak equivalence, consider its action on diagrams $F_*:\operatorname{Fun}(K,A)\to\operatorname{Fun}(K,B)$. Suppose $F_*$ is weak and the shape $K$ has an object $k$.

```agda
module Bicategories.Applications.Categories.Obstruction.Points where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (iso; isoToIsEquiv)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sigma using (Σ-syntax)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.Compose
open import Cubical.Categories.Functor.ComposeProperty
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base using (Bicategory)
open import Bicategories.Instances.Categories using (CATAt)
open import Bicategories.Examples.TerminalComparison using (Terminal)
open import Bicategories.Smallness.Lift using (module LevelLift)
open Functor
open NatTrans
open Category
open isWeakEquivalence

module _ {o h r s t u} (K : Category o h) {A : Category r s} {B : Category t u}
         (F : Functor A B) (k : K .ob) (w : isWeakEquivalence (postcomposeF K F)) where

  private
    module Lifts (a b : A .ob) where
      Ca = Constant K A a
      Cb = Constant K A b
      E : NatTrans Ca Cb ≃ NatTrans (F ∘F Ca) (F ∘F Cb)
      E = F-hom (postcomposeF K F) , w .fullfaith Ca Cb

      liftCell : B [ F ⟅ a ⟆ , F ⟅ b ⟆ ] → NatTrans (F ∘F Ca) (F ∘F Cb)
      liftCell f .N-ob _ = f
      liftCell f .N-hom g = cong (λ g → g ⋆⟨ B ⟩ f) (F .F-id) ∙ B .⋆IdL f
        ∙ sym (cong (B ._⋆_ f) (F .F-id) ∙ B .⋆IdR f)

      pull : B [ F ⟅ a ⟆ , F ⟅ b ⟆ ] → A [ a , b ]
      pull f = invEq E (liftCell f) ⟦ k ⟧

      sec : ∀ f → F ⟪ pull f ⟫ ≡ f
      sec f = cong (_⟦ k ⟧) (secEq E (liftCell f))

      ret : ∀ g → pull (F ⟪ g ⟫) ≡ g
      ret g = cong (_⟦ k ⟧) (cong (invEq E) (makeNatTransPath refl) ∙ retEq E const)
        where
        const : NatTrans Ca Cb
        const .N-ob _ = g
        const .N-hom _ = A .⋆IdL g ∙ sym (A .⋆IdR g)

```

For an arrow $Fa\to Fb$, form the corresponding transformation between constant diagrams. Lift it by full faithfulness of $F_*$ and evaluate at $k$ to get an arrow $a\to b$. For an object $b$, lift the constant diagram at $b$ up to isomorphism and evaluate at $k$ to get a preimage up to isomorphism.

```agda
  postcomposeReflectsWeak : isWeakEquivalence F
  postcomposeReflectsWeak .fullfaith a b =
    isoToIsEquiv (iso _ (Lifts.pull a b) (Lifts.sec a b) (Lifts.ret a b))
  postcomposeReflectsWeak .esssurj b = PT.map atPoint (w .esssurj (Constant K B b))
    where
    atPoint : _ → Σ[ a ∈ A .ob ] CatIso B (F ⟅ a ⟆) b
    atPoint (G , e) = G ⟅ k ⟆ , e .fst ⟦ k ⟧ , FUNCTORIso' K B _ (e .snd) k
```

For the terminal shape every diagram is determined up to natural isomorphism by its value at the unique object. Thus postcomposition with a weak equivalence is itself weak on terminal-shaped diagrams. In the bicategory of categories, postcomposition is the right whiskering functor. Its action on transformations agrees with ordinary postcomposition by the right identity law.

```agda
module _ (k : Level) {o h r s} {A : Category o h} {B : Category r s}
         (F : Functor A B) (w : isWeakEquivalence F) where

  private T = LevelLift.category Terminal k k

  terminalPostWeak : isWeakEquivalence (postcomposeF T F)
  terminalPostWeak .fullfaith = isFullyFaithfulPostcomposeF {C = T} {G = F} (w .fullfaith)
  terminalPostWeak .esssurj H = PT.map point (w .esssurj (H ⟅ lift tt ⟆))
    where
    point : _ → Σ[ G ∈ Functor T A ] CatIso (FUNCTOR T B) (F ∘F G) H
    point (a , e) = Constant T A a , NatIso→FUNCTORIso T B n
      where
      n : NatIso (F ∘F Constant T A a) H
      n .NatIso.trans .N-ob (lift tt) = e .fst
      n .NatIso.trans .N-hom {lift tt} {lift tt} (lift tt) =
        cong (λ g → g ⋆⟨ B ⟩ e .fst) (F .F-id) ∙ B .⋆IdL (e .fst)
        ∙ sym (cong (B ._⋆_ (e .fst)) (H .F-id) ∙ B .⋆IdR (e .fst))
      n .NatIso.nIso (lift tt) = e .snd

catWhiskerPath : ∀ {o h} (K A B : Category o h) (F : Functor A B)
  → Bicategory.rightWhisker (CATAt o h) {K} {A} {B} F ≡ postcomposeF K F
catWhiskerPath K A B F = Functor≡ (λ _ → refl)
  (λ θ → makeNatTransPath (funExt λ k → B .⋆IdR (F ⟪ θ ⟦ k ⟧ ⟫)))
```
