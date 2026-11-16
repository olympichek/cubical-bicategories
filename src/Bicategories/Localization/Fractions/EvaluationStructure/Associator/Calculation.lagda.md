# The associator equation on a common presentation

After evaluating on a common denominator, checking the associator reduces to an ordinary category calculation. The inputs are the four compositor computations and the comparison between the two triangles for the whole triple.

```agda
module Bicategories.Localization.Fractions.EvaluationStructure.Associator.Calculation where

open import Cubical.Foundations.Prelude
open import Bicategories.PathReasoning
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation

open Functor

module _ {o h o′ h′ o″ h″} {A : Category o h} {B : Category o′ h′} {C : Category o″ h″}
  (G : Functor A B) (H : Functor B C) (GH : Functor A C) (compare : NatTrans (H ∘F G) GH) where
  private
    module A = Category A
    module B = Category B
    module C = Category C
    open C using (_⋆_; ⋆Assoc)
    n = NatTrans.N-ob compare

```

Write $\alpha,\beta,\gamma$ for the three single-arrow triangles. Follow both proposed composites by the invertible final triangle. The four pair equations expand the left route to $H(G(\alpha))$ followed by $H(\beta)$ and $\gamma$, and express the right route using the given comparison transformation. Its naturality at $\alpha$ identifies the routes. Cancelling the final triangle gives the result.

```agda
  normalizeTriple : ∀ {a p : A.ob} {b m : B.ob} {left right end : C.ob}
    (α : A [ a , p ]) (β : B [ G ⟅ p ⟆ , b ]) (γ : C [ H ⟅ b ⟆ , end ])
    (fg : B [ G ⟅ a ⟆ , m ]) (pair₁ : B [ m , b ]) (pair₂ : C [ GH ⟅ p ⟆ , end ])
    (κL : C [ H ⟅ m ⟆ , left ]) (κR : C [ GH ⟅ a ⟆ , right ]) (θ : C [ left , right ])
    (triL : C [ left , end ]) (triR : CatIso C right end)
    → fg B.⋆ pair₁ ≡ (G ⟪ α ⟫) B.⋆ β
    → n p ⋆ pair₂ ≡ (H ⟪ β ⟫) ⋆ γ
    → κL ⋆ triL ≡ (H ⟪ pair₁ ⟫) ⋆ γ
    → κR ⋆ triR .fst ≡ (GH ⟪ α ⟫) ⋆ pair₂
    → θ ⋆ triR .fst ≡ triL
    → ((H ⟪ fg ⟫) ⋆ κL) ⋆ θ ≡ n a ⋆ κR
  normalizeTriple {a} {p} α β γ fg pair₁ pair₂ κL κR θ triL triR first second left right assoc =
    ⋆CancelR triR
      ((((H ⟪ fg ⟫) ⋆ κL) ⋆ θ) ⋆ triR .fst
         ≡⟨ ⋆Assoc _ _ _ ⟩
       ((H ⟪ fg ⟫) ⋆ κL) ⋆ (θ ⋆ triR .fst)
         ≡[ i ]⟨ ((H ⟪ fg ⟫) ⋆ κL) ⋆ assoc i ⟩
       ((H ⟪ fg ⟫) ⋆ κL) ⋆ triL
         ≡⟨ ⋆Assoc _ _ _ ⟩
       (H ⟪ fg ⟫) ⋆ (κL ⋆ triL)
         ≡[ i ]⟨ (H ⟪ fg ⟫) ⋆ left i ⟩
       (H ⟪ fg ⟫) ⋆ ((H ⟪ pair₁ ⟫) ⋆ γ)
         ≡˘⟨ ⋆Assoc _ _ _ ⟩
       ((H ⟪ fg ⟫) ⋆ (H ⟪ pair₁ ⟫)) ⋆ γ
         ≡[ i ]⟨ imageFirst i ⋆ γ ⟩
       ((H ⟪ G ⟪ α ⟫ ⟫) ⋆ (H ⟪ β ⟫)) ⋆ γ
         ≡⟨ ⋆Assoc _ _ _ ⟩
       (H ⟪ G ⟪ α ⟫ ⟫) ⋆ ((H ⟪ β ⟫) ⋆ γ)
         ≡[ i ]⟨ (H ⟪ G ⟪ α ⟫ ⟫) ⋆ second (~ i) ⟩
       (H ⟪ G ⟪ α ⟫ ⟫) ⋆ (n p ⋆ pair₂)
         ≡˘⟨ ⋆Assoc _ _ _ ⟩
       ((H ⟪ G ⟪ α ⟫ ⟫) ⋆ n p) ⋆ pair₂
         ≡[ i ]⟨ compare .NatTrans.N-hom α i ⋆ pair₂ ⟩
       (n a ⋆ (GH ⟪ α ⟫)) ⋆ pair₂
         ≡⟨ ⋆Assoc _ _ _ ⟩
       n a ⋆ ((GH ⟪ α ⟫) ⋆ pair₂)
         ≡[ i ]⟨ n a ⋆ right (~ i) ⟩
       n a ⋆ (κR ⋆ triR .fst)
         ≡⟨ sym (⋆Assoc _ _ _) ⟩∎
       (n a ⋆ κR) ⋆ triR .fst)
    where
    imageFirst : (H ⟪ fg ⟫) ⋆ (H ⟪ pair₁ ⟫) ≡ (H ⟪ G ⟪ α ⟫ ⟫) ⋆ (H ⟪ β ⟫)
    imageFirst =
      (H ⟪ fg ⟫) ⋆ (H ⟪ pair₁ ⟫)
        ≡˘⟨ H .F-seq fg pair₁ ⟩
      H ⟪ fg B.⋆ pair₁ ⟫
        ≡[ i ]⟨ H ⟪ first i ⟫ ⟩
      H ⟪ (G ⟪ α ⟫) B.⋆ β ⟫
        ≡⟨ H .F-seq _ β ⟩∎
      (H ⟪ G ⟪ α ⟫ ⟫) ⋆ (H ⟪ β ⟫)
```

The pseudofunctor computation rule is usually written after the inverse associator. Multiplying by the associator gives the normalized triangle used in this calculation.

```agda
module _ {o h} (C : Category o h) where
  open Category C
  normalizePair : ∀ {a b c d e : ob} (α : CatIso C a b)
    (p : C [ b , c ]) (q : C [ c , d ]) (r : C [ a , e ]) (s : C [ e , d ])
    → p ⋆ q ≡ (α .snd .isIso.inv) ⋆ (r ⋆ s) → (α .fst ⋆ p) ⋆ q ≡ r ⋆ s
  normalizePair α p q r s e =
    (α .fst ⋆ p) ⋆ q
      ≡⟨ ⋆Assoc _ _ _ ⟩
    α .fst ⋆ (p ⋆ q)
      ≡[ i ]⟨ α .fst ⋆ e i ⟩
    α .fst ⋆ (α .snd .isIso.inv ⋆ (r ⋆ s))
      ≡˘⟨ ⋆Assoc _ _ _ ⟩
    (α .fst ⋆ α .snd .isIso.inv) ⋆ (r ⋆ s)
      ≡[ i ]⟨ α .snd .isIso.ret i ⋆ (r ⋆ s) ⟩
    id ⋆ (r ⋆ s)
      ≡⟨ ⋆IdL _ ⟩∎
    r ⋆ s
```
