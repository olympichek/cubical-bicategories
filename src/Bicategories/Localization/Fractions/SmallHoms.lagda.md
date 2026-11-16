# Functors between ordinary completions as fraction homs

Write $\eta_G:G\to QG$ for the ordinary completion of each category in the class, with weak unit $\eta_G$. In this model the objects are still the original class members, while the hom from $G$ to $H$ is the category of functors $QG\to QH$ and natural transformations. How does such a functor represent a fraction?

```agda
module Bicategories.Localization.Fractions.SmallHoms where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (isoFunInjective)
open import Cubical.Foundations.Univalence using (pathToEquiv)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.ComposeProperty
open import Cubical.Categories.Equivalence using (WeakInverse)
open import Cubical.Categories.Isomorphism using (invIso)
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors

open import Bicategories.Base using (Bicategory)
open import Bicategories.Instances.Categories using (CAT)
open import Bicategories.FullSubbicategory using (reindex)
open import Bicategories.Smallness.HomCategory as SC using (Sized)
open import Bicategories.Categories.RezkCompletion
open import Bicategories.Localization.Fractions.Composition using (composeRoof)
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.IsoComma

open Category
open Functor
open isWeakEquivalence

module Presentation {ℓ p : Level} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (unit (R G))) where

  open CategoryClass P
  open Roofs P
  open Roof

  smallHoms : Bicategory (ℓ-max (ℓ-suc ℓ) p) ℓ ℓ
  smallHoms = reindex (CAT ℓ) (λ G → completion (R G))

```

Start with a roof $G\xleftarrow{w}A\xrightarrow{n}H$. Since $\eta_G w$ is weak and $QH$ is univalent, $\eta_H n$ extends along $\eta_G w$ to a functor $\widehat r:QG\to QH$. Its characterizing equation is

$$\widehat r\circ\eta_G\circ w=\eta_H\circ n.$$

The code calls this equation `interpretβ`. To identify another functor with $\widehat r$, `identify` asks only for the same equation on $A$.

```agda
  module _ {G H : Object} (r : Roof G H) where
    private
      denominator = unit (R G) ∘F r .left
      descent = fromWeakUnit denominator (univalent (R G))
        (weakComposite (r .leftWeak) (weak G))

    abstract
      interpret : Functor (completion (R G)) (completion (R H))
      interpret = extend descent (univalent (R H)) (unit (R H) ∘F r .right)

      interpretβ : interpret ∘F denominator ≡ unit (R H) ∘F r .right
      interpretβ = extendβ descent (univalent (R H)) (unit (R H) ∘F r .right)

    identify : (F : Functor (completion (R G)) (completion (R H)))
             → F ∘F denominator ≡ unit (R H) ∘F r .right → interpret ≡ F
    identify F eq = isoFunInjective
      (equivToIso (restrictFunctors descent (univalent (R H)))) _ _ (interpretβ ∙ sym eq)

```

Now go in the other direction. For $F:QG\to QH$, use the category of triples $(g,h,i)$ with $i:F(\eta_G g)\cong\eta_H h$ as the apex. Its projection to $G$ is weak and its projection to $H$ is the numerator. The [iso-comma comparison](IsoComma.lagda.md) with components $i$ gives the characterizing equation above, so interpreting this roof recovers $F$.

```agda
  module _ {G H : Object} (F : Functor (completion (R G)) (completion (R H))) where
    private
      module I = IsoComma (F ∘F unit (R G)) (unit (R H))
      module Q = I.FullyFaithful (weak H .fullfaith)

    present : Roof G H
    present = roof
      (I.apex , isoCommaClosed (F ∘F unit (R G)) (unit (R H)) (G .snd) (H .snd))
      I.left (I.isWeakLeft (weak H .esssurj)) Q.right

    interpretPresent : interpret present ≡ F
    interpretPresent = identify present F
      (F-assoc ∙ NatIsoToPath (univalent (R H)) Q.comparisonIso)
```

Over a common refinement, the comparison isomorphism identifies the two denominators after composition with the source unit. Restriction along this weak denominator is fully faithful into the univalent target. Full faithfulness of the target unit recovers the transformation between right legs. Together they identify the cells on the refinement with transformations between the descended functors.

```agda
  module Cells {G H : Object} (r s : Roof G H) where
    open Refinement r s
    private
      ηG = unit (R G)
      ηH = unit (R H)
      d = (ηG ∘F r .left) ∘F I.left
      d' = (ηG ∘F s .left) ∘F Q.right

      weakD : isWeakEquivalence d
      weakD = weakComposite firstWeak (weakComposite (r .leftWeak) (weak G))

      compareBase : d ≡ d'
      compareBase = sym F-assoc
        ∙ NatIsoToPath (univalent (R G)) (ηG ∘ʳi Q.comparisonIso)
        ∙ F-assoc

      rPath : interpret r ∘F d ≡ ηH ∘F (r .right ∘F I.left)
      rPath = F-assoc ∙ cong (_∘F I.left) (interpretβ r) ∙ sym F-assoc

      sPath : interpret s ∘F d ≡ ηH ∘F (s .right ∘F Q.right)
      sPath = cong (interpret s ∘F_) compareBase
        ∙ F-assoc ∙ cong (_∘F Q.right) (interpretβ s) ∙ sym F-assoc

    abstract
      restrictCell : NatTrans (interpret r) (interpret s) ≃ Cell
      restrictCell =
          (_ , isWeakEquiv→isWeakEquivPrecomp (univalent (R H)) d weakD .fullfaith _ _)
        ∙ₑ pathToEquiv (cong₂ NatTrans rPath sPath)
        ∙ₑ invEquiv (_ , isFullyFaithfulPostcomposeF {C = I.apex} {G = ηH}
             (weak H .fullfaith) (r .right ∘F I.left) (s .right ∘F Q.right))
```

Transport identity transformations and vertical composition across `restrictCell`. This gives a category whose objects are the actual roofs and whose arrows are the transformations on their common refinements. The interpretation functor is fully faithful.

```agda
  module Homs (G H : Object) where
    private
      D = FUNCTOR (completion (R G)) (completion (R H))

      onRoofs : Category (ℓ-max (ℓ-suc ℓ) p) ℓ
      onRoofs .ob = Roof G H
      onRoofs .Hom[_,_] r s = D [ interpret r , interpret s ]
      onRoofs .id = D .id
      onRoofs ._⋆_ = D ._⋆_
      onRoofs .⋆IdL = D .⋆IdL
      onRoofs .⋆IdR = D .⋆IdR
      onRoofs .⋆Assoc = D .⋆Assoc
      onRoofs .isSetHom = D .isSetHom

      evaluate : Functor onRoofs D
      evaluate .F-ob = interpret
      evaluate .F-hom f = f
      evaluate .F-id = refl
      evaluate .F-seq _ _ = refl

      codes : Sized (ℓ-max (ℓ-suc ℓ) p) ℓ onRoofs
      codes .fst = Roof G H , idEquiv _
      codes .snd r s = Refinement.Cell r s , invEquiv (Cells.restrictCell r s)

      module V = SC.Resize onRoofs codes

    roofHom : Category (ℓ-max (ℓ-suc ℓ) p) ℓ
    roofHom = V.small

    interpretation : Functor roofHom D
    interpretation = evaluate ∘F V.comparison

    fullyFaithful : isFullyFaithful interpretation
    fullyFaithful = isFullyFaithfulG∘F {F = V.comparison} {G = evaluate}
      V.fullyFaithful (λ _ _ → idIsEquiv _)
```

For a functor between completions, `present` supplies its roof and `interpretPresent` identifies the interpretation. These provide the objectwise choices needed to construct an inverse functor.

```agda
    specifiedInverse : WeakInverse interpretation
    specifiedInverse = inverseFromRepresentatives interpretation fullyFaithful present
      (λ F → pathToIso {C = D} (sym (interpretPresent F)))
```

# Graphs and composition

The interpretation of a graph extends the underlying functor along the source unit. For a composite roof the comparison is the natural square of its iso-comma apex. After whiskering this square with the middle unit, the two descent equations identify the composite of the interpretations as an extension of the composite roof.

```agda
  interpretGraph : {G H : Object} (F : Functor (G .fst) (H .fst))
    → interpret (graph {G} {H} F) ≡ extend (R G) (univalent (R H)) (unit (R H) ∘F F)
  interpretGraph {G} {H} F = identify _ V
    (cong (V ∘F_) F-lUnit ∙ extendβ (R G) (univalent (R H)) (unit (R H) ∘F F))
    where V = extend (R G) (univalent (R H)) (unit (R H) ∘F F)

  interpretCompose : {G H K : Object} (r : Roof G H) (s : Roof H K)
    → interpret (composeRoof P r s) ≡ interpret s ∘F interpret r
  interpretCompose {G} {H} {K} r s = identify _ _
    ( (S ∘F T) ∘F ηG ∘F r .left ∘F I.left
    ≡⟨ Functor≡ (λ _ → refl) (λ _ → refl) ⟩
      (S ∘F (T ∘F (ηG ∘F r .left))) ∘F I.left
    ≡⟨ cong (λ V → (S ∘F V) ∘F I.left) (interpretβ r) ⟩
      (S ∘F (ηH ∘F r .right)) ∘F I.left
    ≡⟨ Functor≡ (λ _ → refl) (λ _ → refl) ⟩
      S ∘F ηH ∘F r .right ∘F I.left
    ≡⟨ cong (S ∘F_) (NatIsoToPath (univalent (R H)) (ηH ∘ʳi Q.comparisonIso)) ⟩
      S ∘F ηH ∘F s .left ∘F Q.right
    ≡⟨ Functor≡ (λ _ → refl) (λ _ → refl) ⟩
      (S ∘F (ηH ∘F s .left)) ∘F Q.right
    ≡⟨ cong (_∘F Q.right) (interpretβ s) ⟩
      (ηK ∘F s .right) ∘F Q.right
    ≡⟨ sym F-assoc ⟩
      ηK ∘F s .right ∘F Q.right ∎ )
    where
    module I = IsoComma (r .right) (s .left)
    module Q = I.FullyFaithful (s .leftWeak .fullfaith)
    S = interpret s
    T = interpret r
    ηG = unit (R G)
    ηH = unit (R H)
    ηK = unit (R K)
```
