# The graph inclusion

The graph of $g:G\to H$ is the roof $G\xleftarrow{1_G}G\xrightarrow{g}H$. We realize this assignment as a pseudofunctor, first using completed functors as arrows and then using roofs themselves.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.Inclusion where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.FullSubcategory
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence

open import Bicategories.Base
open import Bicategories.Equivalence using (InverseData)
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties using (compPseudofunctor)
open import Bicategories.Localization.Base using (Inverts)
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.Bicategory
open import Bicategories.Localization.Fractions.Inversion
open import Bicategories.Categories.RezkCompletion
open import Bicategories.Applications.Categories.CompletionFunctor using (module Construction)

open Bicategory
open Pseudofunctor using (F₀; F₁; Fₕ)

module Inclusion {ℓ p} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (unit (R G))) where
  open CategoryClass P
  open Roofs P
  open Fractions P R weak
  open Presentation P R weak

  open Source P public

```

On the completed functors the graph map is induced by ordinary completion. Pair each graph with its interpretation equation to lift it to the bicategory of *presented* functors. For a weak $g$, the inverse on the completed side is a functor in the opposite direction. Its roof presentation is the reverse graph $H\xleftarrow{g}G\xrightarrow{1_G}G$.

```agda
  smallInclusion : Pseudofunctor source smallHoms
  smallInclusion = Construction.reflection (λ (G : Object) → G .fst) R

  private
    module G = D.LiftFunctor smallInclusion (λ F → graph F , interpretGraph F)

  presentedInclusion : Pseudofunctor source D.presented
  presentedInclusion = G.lifted

  smallInverts : Inverts marked smallInclusion
  smallInverts G H F w .InverseData.inverse = Invert.inverse (R G) (R H) F w (weak H)
  smallInverts G H F w .InverseData.unit = NatIso→FUNCTORIso _ _
    (pathToNatIso (sym (Invert.unitPath (R G) (R H) F w (weak H))))
  smallInverts G H F w .InverseData.counit = NatIso→FUNCTORIso _ _
    (pathToNatIso (Invert.counitPath (R G) (R H) F w (weak H)))

  presentedInverts : Inverts marked presentedInclusion
  presentedInverts G H F w .InverseData.inverse =
    inv , reverseGraph F w , identify _ inv (invβ ∙ sym F-lUnit)
    where
    open Invert (R G) (R H) F w (weak H) renaming (inverse to inv; inverseβ to invβ)
  presentedInverts G H F w .InverseData.unit =
    Incl-Iso-inv _ _ _ _ (smallInverts G H F w .InverseData.unit)
  presentedInverts G H F w .InverseData.counit =
    Incl-Iso-inv _ _ _ _ (smallInverts G H F w .InverseData.counit)

  private
    Target = Σ (Bicategory (ℓ-max (ℓ-suc ℓ) p) (ℓ-max (ℓ-suc ℓ) p) ℓ) (λ B → Pseudofunctor B smallHoms)

    Units : Target → Type _
    Units (B , U) = Σ (Pseudofunctor source B) λ J →
      Σ (Inverts marked J) λ _ → compPseudofunctor U J ≡ smallInclusion

    comparisonPath : Path Target (roofs , forgetRoofs) (D.presented , D.forget)
    comparisonPath i = roofsPath i , forgetRoofsPath i

    opaque
      presentedGraphUnit : Units (D.presented , D.forget)
      presentedGraphUnit .fst = presentedInclusion
      presentedGraphUnit .snd .fst = presentedInverts
      presentedGraphUnit .snd .snd = G.forgetLift

    opaque
      graphUnit : Units (roofs , forgetRoofs)
      graphUnit = subst {A = Target} Units (sym comparisonPath) presentedGraphUnit

```

Transport the presented graph inclusion and its inversion data along the identification with the bicategory of actual roofs. The resulting `compatible` equation says that interpreting an included graph recovers `smallInclusion`.

```agda
  inclusion : Pseudofunctor source roofs
  inclusion = graphUnit .fst

  opaque
    unfolding graphUnit presentedGraphUnit
    inclusionPath : PathP (λ i → Pseudofunctor source (roofsPath i)) inclusion presentedInclusion
    inclusionPath i = subst-filler Units (sym comparisonPath) presentedGraphUnit (~ i) .fst

  compatible : compPseudofunctor forgetRoofs inclusion ≡ smallInclusion
  compatible = graphUnit .snd .snd

  inclusionInverts : Inverts marked inclusion
  inclusionInverts = graphUnit .snd .fst
```
