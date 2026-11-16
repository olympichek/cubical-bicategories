# Classes of groupoids closed under iso-comma roofs

The fraction construction applies to groupoids and strict groupoids once their object classes are shown to be closed under the iso-comma construction.

```agda
module Bicategories.Localization.Fractions.Instances where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Bicategories.Instances.Groupoids using (isGroupoidCategory)
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.IsoComma

open CategoryClass

```

In the full-subcategory construction of the iso-comma apex, an arrow is an arrow of its first source category. In a groupoid, its inverse there already satisfies both inverse equations in the iso-comma category.

```agda
groupoids : ∀ ℓ → CategoryClass ℓ ℓ
groupoids ℓ .Member = isGroupoidCategory
groupoids ℓ .isoCommaClosed E q g h r s f =
  let i = g (r .fst) (s .fst) f in isiso (isIso.inv i) (isIso.sec i) (isIso.ret i)

```

For strict groupoids we also need the type of objects to be a set. Such an object consists of two source objects and a comparison isomorphism. Setness of the two object types gives setness of these triples via `isSetApex`.

```agda
strictGroupoids : ∀ ℓ → CategoryClass ℓ ℓ
strictGroupoids ℓ .Member C = isSet (Category.ob C) × isGroupoidCategory C
strictGroupoids ℓ .isoCommaClosed E q (sG , g) (sH , h) =
  IsoComma.isSetApex E q sG sH , groupoids ℓ .isoCommaClosed E q g h
```
