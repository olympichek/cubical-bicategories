# Finite object families

A single arrow has two endpoints. A composable pair has three, and a composable triple has four. We package these lists of objects as families indexed by $\mathrm{Fin}(n)$ so that the same descent theorem can handle each arity.

```agda
module Bicategories.WeakBiequivalence.Descent.Tuples where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc; _+_)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.SumFin.Base using (Fin; fzero; fsuc)

i₀ : ∀ {n} → Fin (1 + n)
i₀ = fzero

i₁ : ∀ {n} → Fin (2 + n)
i₁ = fsuc fzero

i₂ : ∀ {n} → Fin (3 + n)
i₂ = fsuc (fsuc fzero)

two : ∀ {ℓ} {X : Type ℓ} → X → X → Fin 2 → X
two x y fzero = x
two x y (fsuc fzero) = y

twoη : ∀ {ℓ} {X : Type ℓ} (v : Fin 2 → X) → v ≡ two (v i₀) (v i₁)
twoη v = funExt λ { fzero → refl ; (fsuc fzero) → refl }

three : ∀ {ℓ} {X : Type ℓ} → X → X → X → Fin 3 → X
three x y z fzero = x
three x y z (fsuc fzero) = y
three x y z (fsuc (fsuc fzero)) = z

i₃ : ∀ {n} → Fin (4 + n)
i₃ = fsuc (fsuc (fsuc fzero))

four : ∀ {ℓ} {X : Type ℓ} → X → X → X → X → Fin 4 → X
four w x y z fzero = w
four w x y z (fsuc fzero) = x
four w x y z (fsuc (fsuc fzero)) = y
four w x y z (fsuc (fsuc (fsuc fzero))) = z
```

For a finite family $P$, pointwise mere existence of $P(i)$ implies mere existence of a section. Writing $\lVert -\rVert$ for propositional truncation, the map has type

$$
\left(\prod_{i:\mathrm{Fin}(n)}\lVert P(i)\rVert\right)\;\longrightarrow\;\left\lVert\prod_{i:\mathrm{Fin}(n)} P(i)\right\rVert.
$$

Induct on the number of indices. The empty section needs no data, and in the successor case we combine a representative at the first index with a section for the remaining ones. The result still lies under truncation.

```agda
chooseFinite : ∀ {ℓ} {n : ℕ} (P : Fin n → Type ℓ)
               → ((x : Fin n) → PT.∥ P x ∥₁) → PT.∥ ((x : Fin n) → P x) ∥₁
chooseFinite {n = zero} P p = PT.∣ (λ ()) ∣₁
chooseFinite {n = suc n} P p = PT.rec2 PT.squash₁
    (λ head tail → PT.∣ (λ { fzero → head ; (fsuc x) → tail x }) ∣₁)
    (p fzero) (chooseFinite (λ x → P (fsuc x)) (λ x → p (fsuc x)))
```
