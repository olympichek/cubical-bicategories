# The path groupoid of the circle

What does a univalent groupoid with a non-set of objects look like? Take the points of the circle as objects and paths as arrows. The circle is a 1-type, so the paths between two fixed points form a set, as required for a hom-set.

```agda
module Bicategories.Examples.CircleGroupoid where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Data.Int using (pos; injPos)
open import Cubical.Data.Nat using (znots)
open import Cubical.HITs.S1
open import Cubical.Relation.Nullary using (¬_)
open import Bicategories.Base
open import Bicategories.Instances.Groupoids

circleGroupoid : Bicategory.Ob (UNIVGPD ℓ-zero)
circleGroupoid = pathGroupoid (S¹ , isGroupoidS¹)

private C = circleGroupoid .fst .fst

```

In a path groupoid, an arrow from an object to itself is a loop at that point. At the base point of $S^1$, `intLoop` constructs one such arrow for each integer. Take the arrows for $0$ and $1$.

```agda
constantLoop windingOne : C [ base , base ]
constantLoop = intLoop (pos 0)
windingOne   = intLoop (pos 1)

```

An equality of these arrows would give an equality of winding numbers. The calculation `windingℤLoop` evaluates the two sides to $0$ and $1$. If the object type were a set, any two paths from the base point to itself would be equal, giving exactly the equality just ruled out.

```agda
distinctLoops : ¬ (constantLoop ≡ windingOne)
distinctLoops p = znots (injPos (sym (windingℤLoop (pos 0))
                               ∙ cong winding p ∙ windingℤLoop (pos 1)))

objectsAreNotASet : ¬ isSet (Category.ob C)
objectsAreNotASet s = distinctLoops (s base base constantLoop windingOne)
```
