# Removing identity denominators

When a denominator is isomorphic to an identity arrow, removing it uses the unitors of the target bicategory. The calculations below keep track of this removal while a second arrow is composed on either side.

```agda
module Bicategories.Localization.Fractions.EvaluationGraph.Padding where

open import Cubical.Foundations.Prelude hiding (_▷_; _◁_; comp)
open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Bicategories.Base
open import Bicategories.Coherence
open import Bicategories.Equivalence.Whiskering

module Padding {o h c} (T : Bicategory o h c) where
  open Bicategory T

```

Fix $s:1_x\cong w$. To insert $w$ in front of $v$, first write $v$ as $1_x\star v$ using the inverse left unitor, then whisker $s$ by $v$. These components form a natural isomorphism, giving `insertNatural`. At an identity arrow the right unitor takes the inserted component back to $s$.

```agda
  module _ {x : Ob} {w : Cell x x} (s : CatIso (hom x x) (id₁ x) w) where
    insert : ∀ {y} (v : Cell x y) → Two v (w ⋆₁ v)
    insert v = leftUnitor v .snd .isIso.inv ⋆₂ (s .fst ▷ v)

    private
      insertion : ∀ {y} → NatIso Id (leftWhisker {z = y} w)
      insertion = symNatIso (seqNatIso (changingLeftWhisker T (invIso s)) (leftWhiskerUnitor T))

    insertNatural : ∀ {y} {v v′ : Cell x y} (a : Two v v′)
      → a ⋆₂ insert v′ ≡ insert v ⋆₂ (w ◁ a)
    insertNatural a = NatTrans.N-hom (insertion .NatIso.trans) a

    insertIdentity : insert (id₁ x) ⋆₂ rightUnitor w .fst ≡ s .fst
    insertIdentity = K.⋆Assoc _ _ _ ∙ cong (u .snd .isIso.inv ⋆₂_) (rightUnitor-natural (s .fst))
      ∙ sym (K.⋆Assoc _ _ _) ∙ cong (_⋆₂ s .fst)
        (cong (u .snd .isIso.inv ⋆₂_) (sym (unitors-id x)) ∙ u .snd .isIso.sec)
      ∙ K.⋆IdL _
      where
      module K = Category (hom x x)
      u = leftUnitor (id₁ x)

```

Now insert $w$ before a composite $f\star g$. Reassociating at the end should give the insertion before $f$ whiskered by $g$. The left-unit law for $f\star g$ gives the equation between unitors. Naturality of the associator moves $s$ through that equation.

```agda
    insertComposite : ∀ {y z} (f : Cell x y) (g : Cell y z) →
      insert (f ⋆₁ g) ⋆₂ (associator w f g .snd .isIso.inv) ≡ insert f ▷ g
    insertComposite {z = z} f g = sym (⋆InvRMove (associator w f g)
      (cong (_⋆₂ associator w f g .fst) (Functor.F-seq (rightWhisker g) _ _)
       ∙ K.⋆Assoc _ _ _ ∙ cong ((leftUnitor f .snd .isIso.inv ▷ g) ⋆₂_) (assocNatR T (s .fst) f g)
       ∙ sym (K.⋆Assoc _ _ _) ∙ cong (_⋆₂ (s .fst ▷ (f ⋆₁ g))) base))
      where
      module K = Category (hom x z)
      u = leftUnitor (f ⋆₁ g)
      base : (leftUnitor f .snd .isIso.inv ▷ g) ⋆₂ associator (id₁ x) f g .fst ≡ u .snd .isIso.inv
      base = ⋆CancelR u (K.⋆Assoc _ _ _
        ∙ cong ((leftUnitor f .snd .isIso.inv ▷ g) ⋆₂_) (leftUnitComposite T f g)
        ∙ F-Iso {F = rightWhisker g} (leftUnitor f) .snd .isIso.sec ∙ sym (u .snd .isIso.sec))

```

To insert $w$ between $f$ and $g$, start with the inverse right unitor of $f$. The triangle for $f,1_x,g$ identifies that choice with the inverse left unitor of $g$. Naturality at $s$ then yields $f\mathbin{\triangleleft}\operatorname{insert}(g)$.

```agda
    insertMiddle : ∀ {y z} (f : Cell y x) (g : Cell x z) →
      ((rightUnitor f .snd .isIso.inv ▷ g) ⋆₂ ((f ◁ s .fst) ▷ g))
      ⋆₂ associator f w g .fst ≡ f ◁ insert g
    insertMiddle {y} {z} f g =
      K.⋆Assoc _ _ _ ∙ cong ((rightUnitor f .snd .isIso.inv ▷ g) ⋆₂_) (assocNatM T f (s .fst) g)
      ∙ sym (K.⋆Assoc _ _ _) ∙ cong (_⋆₂ (f ◁ (s .fst ▷ g))) base
      ∙ sym (Functor.F-seq (leftWhisker f) _ _)
      where
      module K = Category (hom y z)
      u = F-Iso {F = leftWhisker f} (leftUnitor g)
      base : (rightUnitor f .snd .isIso.inv ▷ g) ⋆₂ associator f (id₁ x) g .fst ≡ u .snd .isIso.inv
      base = ⋆CancelR u (K.⋆Assoc _ _ _
        ∙ cong ((rightUnitor f .snd .isIso.inv ▷ g) ⋆₂_) (triangle f g)
        ∙ F-Iso {F = rightWhisker g} (rightUnitor f) .snd .isIso.sec ∙ sym (u .snd .isIso.sec))
```
