# Detecting the unitor laws on a denominator

Let $\tau:d\star v\cong n$ be an evaluation triangle, and suppose whiskering by $d$ is faithful. To prove a unitor law for $v$, we can whisker the proposed equation by $d$ and follow both sides by $\tau$.

```agda
module Bicategories.Localization.Fractions.EvaluationStructure.UnitLaws.Pasting where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_; comp)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism using (invFlipSq; isIso→areInv)
open import Bicategories.Base
open import Bicategories.Coherence using (assocNatM; assocNatL; rightUnitComposite)
open import Bicategories.Equivalence.Whiskering using (interchange)

private
  module _ {a b} (C : Category a b) where
    open Category C

    move : ∀ {v w x y z} {p : Hom[ v , w ]} {q : Hom[ w , y ]}
      {r : Hom[ v , x ]} {s : Hom[ x , y ]}
      → p ⋆ q ≡ r ⋆ s → (t : Hom[ y , z ]) → p ⋆ (q ⋆ t) ≡ r ⋆ (s ⋆ t)
    move eq t = sym (⋆Assoc _ _ t) ∙ cong (_⋆ t) eq ∙ ⋆Assoc _ _ t

    merge : ∀ {v x y z} {p : Hom[ v , x ]} {q : Hom[ x , y ]} {r : Hom[ v , y ]}
      → p ⋆ q ≡ r → (t : Hom[ y , z ]) → p ⋆ (q ⋆ t) ≡ r ⋆ t
    merge eq t = sym (⋆Assoc _ _ t) ∙ cong (_⋆ t) eq

  module _ {a b c d} {C : Category a b} {D : Category c d} (K : Functor C D) where
    module C = Category C
    module D = Category D

    expand : ∀ {s t u v w} (p : C.Hom[ s , t ]) (q : C.Hom[ t , u ]) (r : C.Hom[ u , v ])
      (z : D.Hom[ K ⟅ v ⟆ , w ]) → ((K ⟪ (p C.⋆ q) C.⋆ r ⟫) D.⋆ z)
      ≡ (K ⟪ p ⟫ D.⋆ (K ⟪ q ⟫ D.⋆ (K ⟪ r ⟫ D.⋆ z)))
    expand p q r z = cong (D._⋆ z) (Functor.F-seq K _ _)
      ∙ D.⋆Assoc _ _ _ ∙ cong (D._⋆ (K ⟪ r ⟫ D.⋆ z)) (Functor.F-seq K _ _) ∙ D.⋆Assoc _ _ _

```

Applying the whiskering functor to a composite exposes its three cells individually. The helpers above allow us to replace a pair inside this composite using its equation, leaving the final cell in place. The two operations of whiskering by $d$ and then appending $\tau$ together detect equality.

```agda
module Detect {o h c} (D : Bicategory o h c) {z x y} (d : Bicategory.Cell D z x)
  (v : Bicategory.Cell D x y) {n : Bicategory.Cell D z y}
  (τ : CatIso (Bicategory.hom D z y) (Bicategory._⋆₁_ D d v) n)
  (faith : Functor.isFaithful (Bicategory.leftWhisker D {z = y} d)) where

  open Bicategory D
  private
    H = hom z y
    W = leftWhisker {z = y} d
    A⁻ = λ {a b c e} (f : Cell a b) (g : Cell b c) (k : Cell c e) → associator f g k .snd .isIso.inv

```

For the left unitor the identity triangle is based at $d$. Use the computation for the source unitor and then the compositor to expand the whiskered left side. Naturality of the associator moves the unit comparison next to its identity triangle. They combine to the right unitor of $d$, and the bicategory triangle axiom gives the desired left unitor at $v$.

```agda
  left : {e : Cell x x} {v′ : Cell x y}
    (ε : Two (id₁ x) e) (μ : Two (e ⋆₁ v) v′) (l : Two v′ v)
    (idTriangle : Two (d ⋆₁ e) d) (compositeTriangle : Two (d ⋆₁ v′) n)
    → (d ◁ ε) ⋆₂ idTriangle ≡ rightUnitor d .fst
    → (d ◁ μ) ⋆₂ compositeTriangle ≡ A⁻ d e v ⋆₂ ((idTriangle ▷ v) ⋆₂ τ .fst)
    → (d ◁ l) ⋆₂ τ .fst ≡ compositeTriangle
    → (((ε ▷ v) ⋆₂ μ) ⋆₂ l) ≡ leftUnitor v .fst
  left {e} ε μ l u comp unitβ compβ cellβ = faith _ _ _ _ (⋆CancelR τ calculation)
    where
    a₀ = associator d (id₁ x) v
    a₁ = associator d e v
    slide = invFlipSq (isIso→areInv (a₀ .snd)) (isIso→areInv (a₁ .snd)) (assocNatM D d ε v)
    join = sym (Functor.F-seq (rightWhisker v) (d ◁ ε) u) ∙ cong (_▷ v) unitβ
    calculation = expand W (ε ▷ v) μ l (τ .fst)
      ∙ cong ((d ◁ (ε ▷ v)) ⋆₂_) (cong ((d ◁ μ) ⋆₂_) cellβ ∙ compβ)
      ∙ move H slide ((u ▷ v) ⋆₂ τ .fst)
      ∙ cong (a₀ .snd .isIso.inv ⋆₂_) (merge H join (τ .fst))
      ∙ merge H (sym (⋆InvLMove a₀ (triangle d v))) (τ .fst)
```

For the right unitor, interchange slides the unit comparison through the evaluation triangle before its computation rule is used. Naturality of the right unitor and its law on a composite finish the calculation.

```agda
  right : {e : Cell y y} {v′ : Cell x y}
    (ε : Two (id₁ y) e) (μ : Two (v ⋆₁ e) v′) (r : Two v′ v)
    (idTriangle : Two (n ⋆₁ e) n) (compositeTriangle : Two (d ⋆₁ v′) n)
    → (n ◁ ε) ⋆₂ idTriangle ≡ rightUnitor n .fst
    → (d ◁ μ) ⋆₂ compositeTriangle ≡ A⁻ d v e ⋆₂ ((τ .fst ▷ e) ⋆₂ idTriangle)
    → (d ◁ r) ⋆₂ τ .fst ≡ compositeTriangle
    → (((v ◁ ε) ⋆₂ μ) ⋆₂ r) ≡ rightUnitor v .fst
  right {e} ε μ r u comp unitβ compβ cellβ = faith _ _ _ _ (⋆CancelR τ calculation)
    where
    a₀ = associator d v (id₁ y)
    a₁ = associator d v e
    slide = invFlipSq (isIso→areInv (a₀ .snd)) (isIso→areInv (a₁ .snd)) (assocNatL D d v ε)
    pass = move H (interchange D (τ .fst) ε) u
         ∙ cong ((τ .fst ▷ id₁ y) ⋆₂_) unitβ ∙ rightUnitor-natural (τ .fst)
    calculation = expand W (v ◁ ε) μ r (τ .fst)
      ∙ cong ((d ◁ (v ◁ ε)) ⋆₂_) (cong ((d ◁ μ) ⋆₂_) cellβ ∙ compβ)
      ∙ move H slide ((τ .fst ▷ e) ⋆₂ u)
      ∙ cong (a₀ .snd .isIso.inv ⋆₂_) pass
      ∙ merge H (sym (⋆InvLMove a₀ (rightUnitComposite D d v))) (τ .fst)
```
