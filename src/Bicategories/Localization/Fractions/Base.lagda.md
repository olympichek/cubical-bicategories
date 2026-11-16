# Roofs and their common refinements

We will use a span of functors to represent a fraction. The [iso-comma construction](IsoComma.lagda.md) supplies the common source needed for [composition](Composition.lagda.md). Its middle category has to stay in the chosen class when we compose fractions or compare two of them.

```agda
module Bicategories.Localization.Fractions.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Localization.Fractions.IsoComma

open Category
open Functor
open isWeakEquivalence

```

For $E:G\to U$ and $q:H\to U$, form the category of triples $(g,h,i)$ with $i:E(g)\cong q(h)$ and arrows inherited from $G$. The class must contain this category whenever it contains $G$ and $H$. Only the hom-sets of $U$ must fit in level $\ell$. For a fully faithful $q$, the arrow of $H$ making each comparison square commute is uniquely determined, so the triples describe the usual iso-comma category. This applies when $q$ is a denominator. Both the class of all small categories and the class of categories with a set of objects satisfy the closure condition.

```agda
record CategoryClass (ℓ p : Level) : Typeω where
  field
    Member : Category ℓ ℓ → Type p
    isoCommaClosed : ∀ {u} {G H : Category ℓ ℓ} {U : Category u ℓ}
                   → (E : Functor G U) (q : Functor H U)
                   → Member G → Member H → Member (IsoComma.apex E q)

  Object : Type (ℓ-max (ℓ-suc ℓ) p)
  Object = Σ (Category ℓ ℓ) Member

open CategoryClass

allCategories : (ℓ : Level) → CategoryClass ℓ ℓ-zero
allCategories ℓ .Member C = Unit
allCategories ℓ .isoCommaClosed E q _ _ = tt

strictCategories : (ℓ : Level) → CategoryClass ℓ ℓ
strictCategories ℓ .Member C = isSet (C .ob)
strictCategories ℓ .isoCommaClosed E q = IsoComma.isSetApex E q

private variable
  ℓ p : Level

open import Bicategories.Categories.WeakEquivalence public using (weakId; weakComposite)

```

A roof from $G$ to $H$ consists of

$$G\xleftarrow{w}A\xrightarrow{n}H,$$

where $w$ is fully faithful and essentially surjective. Think of $n$ as the numerator and $w$ as the denominator. An ordinary functor gives the roof with identity denominator (`graph`). A weak functor also gives a roof in the opposite direction with identity numerator (`reverseGraph`).

```agda
module Roofs (P : CategoryClass ℓ p) where

  record Roof (G H : Object P) : Type (ℓ-max (ℓ-suc ℓ) p) where
    constructor roof
    field
      middle : Object P
      left : Functor (middle .fst) (G .fst)
      leftWeak : isWeakEquivalence left
      right : Functor (middle .fst) (H .fst)

  open Roof

  graph : {G H : Object P} → Functor (G .fst) (H .fst) → Roof G H
  graph {G} F = roof G Id (weakId _) F

  reverseGraph : {G H : Object P} (F : Functor (G .fst) (H .fst))
               → isWeakEquivalence F → Roof H G
  reverseGraph {G} F w = roof G F w Id
```

To compare two roofs, form the iso-comma category of their denominators over $G$. Both projections $\pi_1,\pi_2$ are weak. A cell from the first roof to the second is a natural transformation $n_1\pi_1\Rightarrow n_2\pi_2$ between the numerators on this common source.

```agda
  module Refinement {G H : Object P} (r s : Roof G H) where
    module I = IsoComma (r .left) (s .left)
    module Q = I.FullyFaithful (s .leftWeak .fullfaith)

    common : Object P
    common = I.apex , P .isoCommaClosed (r .left) (s .left) (r .middle .snd) (s .middle .snd)

    firstWeak : isWeakEquivalence I.left
    firstWeak = I.isWeakLeft (s .leftWeak .esssurj)

    secondWeak : isWeakEquivalence Q.right
    secondWeak = Q.isWeakRight (r .leftWeak)

    Cell : Type ℓ
    Cell = NatTrans (r .right ∘F I.left) (s .right ∘F Q.right)

    isSetCell : isSet Cell
    isSetCell = isSetNatTrans
```
