# Horizontal pasting of evaluated triangles

Naturality of the compositor requires one equation between pasted triangles. The common middle leg contributes a 2-cell to the first triangle and accepts that same cell on the boundary of the second.

```agda
module Bicategories.Localization.Fractions.EvaluationStructure.Naturality.Pasting where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism using (invFlipSq; CatIso→areInv; compSq)
open import Bicategories.Base

module Pasting {o h c} (T : Bicategory o h c) where
  open Bicategory T

  module _ {x y z w : Ob} (d : Cell x y) {f f′ : Cell y z} {g g′ : Cell z w}
    {n n′ : Cell x z} {m m′ : Cell x w}
    (a : Two (d ⋆₁ f) n) (a′ : Two (d ⋆₁ f′) n′)
    (b : Two (n ⋆₁ g) m) (b′ : Two (n′ ⋆₁ g′) m′) where
    private
      H = hom x w

```

Suppose the change at the middle leg is $\nu$ and the change at the last is $\omega$. Naturality of the inverse associator moves the horizontal change $\sigma\otimes\tau$ to the first triangle. Functoriality of horizontal composition then exposes its square with $\nu$. Pasting the remaining square reaches $\omega$.

```agda
    horizontal : (σ : Two f f′) (τ : Two g g′) (ν : Two n n′) (ω : Two m m′)
      → (d ◁ σ) ⋆₂ a′ ≡ a ⋆₂ ν → (ν ⊗ τ) ⋆₂ b′ ≡ b ⋆₂ ω
      → (d ◁ (σ ⊗ τ)) ⋆₂ (invIso (associator d f′ g′) .fst ⋆₂ (a′ ▷ g′) ⋆₂ b′)
      ≡ (invIso (associator d f g) .fst ⋆₂ (a ▷ g) ⋆₂ b) ⋆₂ ω
    horizontal σ τ ν ω e s = compSq H first (compSq H middle s)
      where
      first : (d ◁ (σ ⊗ τ)) ⋆₂ invIso (associator d f′ g′) .fst
            ≡ invIso (associator d f g) .fst ⋆₂ ((d ◁ σ) ⊗ τ)
      first = invFlipSq (CatIso→areInv (associator d f g)) (CatIso→areInv (associator d f′ g′))
        (associator-natural (id₂ d) σ τ)
      middle : ((d ◁ σ) ⊗ τ) ⋆₂ (a′ ▷ g′) ≡ (a ▷ g) ⋆₂ (ν ⊗ τ)
      middle = sym (Functor.F-seq comp _ _) ∙ cong₂ _⊗_ e
        (Category.⋆IdR (hom z w) τ ∙ sym (Category.⋆IdL (hom z w) τ))
        ∙ Functor.F-seq comp _ _

```

The middle square itself can be built in two pieces. Change $g$ at fixed $n$, then change $n$ at fixed $g'$. The horizontal composite $\nu\otimes\tau$ is exactly this composite of whiskerings, so the output is the composite of the two changes $\xi$ then $\rho$.

```agda
  module _ {x y z : Ob} {n n′ : Cell x y} {g g′ : Cell y z}
    {l m r : Cell x z} (a : Two (n ⋆₁ g) l) (b : Two (n ⋆₁ g′) m) (c′ : Two (n′ ⋆₁ g′) r) where
    merge : (ν : Two n n′) (τ : Two g g′) (ξ : Two l m) (ρ : Two m r)
      → (n ◁ τ) ⋆₂ b ≡ a ⋆₂ ξ → (ν ▷ g′) ⋆₂ c′ ≡ b ⋆₂ ρ
      → (ν ⊗ τ) ⋆₂ c′ ≡ a ⋆₂ (ξ ⋆₂ ρ)
    merge ν τ ξ ρ e s = cong (_⋆₂ c′) (cong₂ _⊗_ (sym (Category.⋆IdL (hom x y) ν))
      (sym (Category.⋆IdR (hom y z) τ)) ∙ Functor.F-seq comp _ _)
      ∙ Category.⋆Assoc H _ _ _ ∙ cong ((n ◁ τ) ⋆₂_) s
      ∙ sym (Category.⋆Assoc H _ _ _) ∙ cong (_⋆₂ ρ) e ∙ Category.⋆Assoc H _ _ _
      where H = hom x z
```
