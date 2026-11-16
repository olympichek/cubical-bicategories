# Changing the endpoints of an isomorphism

An isomorphism lets us change either endpoint of a second isomorphism. We need the resulting map on isomorphism types to be an equivalence.

```agda
module Bicategories.Categories.Isomorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Isomorphism
module _ {o c} (C : Category o c) where
  open Category C
  open isIso

```

For $e:x\cong y$, precomposition sends $k:y\cong z$ to $k\circ e:x\cong z$. Precomposing with $e^{-1}$ gives its inverse.

```agda
  preIsoEquiv : ∀ {x y z} (e : CatIso C x y) → CatIso C y z ≃ CatIso C x z
  preIsoEquiv e = isoToEquiv (iso (⋆Iso e) (⋆Iso (invIso e))
    (λ k → CatIso≡ _ _ (sym (⋆Assoc _ _ _) ∙ cong₂ _⋆_ (e .snd .ret) refl ∙ ⋆IdL _))
    (λ k → CatIso≡ _ _ (sym (⋆Assoc _ _ _) ∙ cong₂ _⋆_ (e .snd .sec) refl ∙ ⋆IdL _)))

```

At the other endpoint, $e:y\cong z$ sends $k:x\cong y$ to $e\circ k:x\cong z$. This time the inverse postcomposes with $e^{-1}$.

```agda
  postIsoEquiv : ∀ {x y z} (e : CatIso C y z) → CatIso C x y ≃ CatIso C x z
  postIsoEquiv e = isoToEquiv (iso (λ k → ⋆Iso k e) (λ k → ⋆Iso k (invIso e))
    (λ k → CatIso≡ _ _ (⋆Assoc _ _ _ ∙ cong₂ _⋆_ refl (e .snd .sec) ∙ ⋆IdR _))
    (λ k → CatIso≡ _ _ (⋆Assoc _ _ _ ∙ cong₂ _⋆_ refl (e .snd .ret) ∙ ⋆IdR _)))
```
