# Composition of roofs

A roof represents an arrow using a weak equivalence as a denominator. To compose $G\xleftarrow{w}A\xrightarrow{u}H$ with $H\xleftarrow{v}B\xrightarrow{t}K$, first match objects from $A$ and $B$ over $H$.

```agda
module Bicategories.Localization.Fractions.Composition where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence.WeakEquivalence

open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.IsoComma

module _ {ℓ p : Level} (P : CategoryClass ℓ p) where
  open CategoryClass P
  open Roofs P
  open Roof
  open isWeakEquivalence

```

An object of the [iso-comma category](IsoComma.lagda.md) is a pair $(a,b)$ with an isomorphism $u(a)\cong v(b)$. Its projections give the composite roof

$$G\xleftarrow{w\circ\pi_1}(u\downarrow_{\cong}v)\xrightarrow{t\circ\pi_2}K.$$

Essential surjectivity of $v$ makes $\pi_1$ essentially surjective. Full faithfulness of $v$ supplies the action of $\pi_2$ on arrows. The new denominator is weak, and closure under iso-comma categories keeps the new apex in the chosen class.

```agda
  composeRoof : {G H K : Object} → Roof G H → Roof H K → Roof G K
  composeRoof r s = roof
    (I.apex , isoCommaClosed (r .right) (s .left) (r .middle .snd) (s .middle .snd))
    (r .left ∘F I.left)
    (weakComposite (I.isWeakLeft (s .leftWeak .esssurj)) (r .leftWeak))
    (s .right ∘F Q.right)
    where
    module I = IsoComma (r .right) (s .left)
    module Q = I.FullyFaithful (s .leftWeak .fullfaith)
```
