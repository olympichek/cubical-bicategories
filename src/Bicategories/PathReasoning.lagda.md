# Equational reasoning

Cubical’s prelude writes a path from $x$ to $y$ as a step `x ≡⟨ p ⟩ y` in a calculation. Use `x ≡˘⟨ p ⟩ y` when the available path runs from $y$ to $x$. A step `x ≡[ i ]⟨ f (p i) ⟩ y` displays how a path acts under a function.

```agda
module Bicategories.PathReasoning where

open import Cubical.Foundations.Prelude

infixr 2 _≡˘⟨_⟩_
_≡˘⟨_⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A} → y ≡ x → y ≡ z → x ≡ z
x ≡˘⟨ p ⟩ q = sym p ∙ q

```

Close a chain with `∎` when the last line is reflexivity. When the last justification already has the required endpoints, `x ≡⟨ p ⟩∎ y` returns $p$ directly. This matters in definitions where Agda needs the final expression to reduce to that proof.

```agda
last-step : ∀ {ℓ} {A : Type ℓ} (x y : A) → x ≡ y → x ≡ y
last-step _ _ p = p

infixr 2 last-step
syntax last-step x y p = x ≡⟨ p ⟩∎ y
```
