# Universe-preserving bicategorical Rezk completion

Starting with any bicategory $B$, we want a univalent bicategory and a map from $B$ that induces a weak equivalence on each hom and reaches every object up to adjoint equivalence. The construction has two stages. It first makes the hom categories univalent, then uses Yoneda to impose univalence on the objects.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.RezkCompletion.Construction.Small where

open import Cubical.Foundations.Prelude
open import Bicategories.RezkCompletion.Base using (RezkCompletion)
open import Bicategories.RezkCompletion.Criterion using (makeIsRezkCompletion)
open import Bicategories.Base
open import Bicategories.RezkCompletion.Construction.Resize
open import Bicategories.RezkCompletion.Construction.Yoneda

```

Write $L B$ for the homwise completion. `Source` constructs it, `Y` embeds it into a bicategory of presheaves, and `Result` resizes the full essential image of that embedding. The two units compose to give the desired map

$$
B \longrightarrow L B \longrightarrow \operatorname{RC}_2(B).
$$

```agda
module Small {o h c} (B : Bicategory o h c) where
  private
    module Source = FromLocal B
    module Y = Large Source.H.completion Source.H.isLocallyUnivalent
    module Result = Source.FromLarge {D = Y.completion} Y.unit Y.isUnivalentCompletion
                                     Y.isWeakBiequivalenceUnit

  open Result public using (witness) renaming
    (small to Rezk; unit to →Rezk; weakUnit to isWeakBiequivalence→Rezk;
     isUnivalentSmall to isUnivalentRezk)

```

The weak biequivalence $\eta_B:B\to\operatorname{RC}_2(B)$ and the univalence of its target imply the universal property by `makeIsRezkCompletion`. The type of `package` records the size bound explicitly. If the levels for objects, 1-cells and 2-cells of $B$ are $o,h,c$, the completion uses $o\sqcup h\sqcup c$, $h\sqcup c$ and $c$, respectively.

```agda
  package : RezkCompletion B (ℓ-max o (ℓ-max h c)) (ℓ-max h c) c
  package .RezkCompletion.completion = Rezk
  package .RezkCompletion.unit = →Rezk
  package .RezkCompletion.isCompletion =
    makeIsRezkCompletion {B = B} {R = Rezk} →Rezk isUnivalentRezk isWeakBiequivalence→Rezk

open Small public
```
