# The double delooping of the group of order two

This bicategory has one object and one 1-cell. Its 2-endomorphisms are Booleans with addition modulo two as both vertical and horizontal composition. Commutativity gives interchange, while every structural 2-cell is the identity. Consequently a locally weak equivalence must still distinguish the two 2-automorphisms in its target.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Examples.DoubleDelooping where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Properties using (isFullyFaithful→Faithful)
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Cubical.Data.Bool
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Relation.Nullary using (¬_)
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.WeakBiequivalence.Base

private
  H : Category ℓ-zero ℓ-zero
  H .Category.ob = Unit
  H .Category.Hom[_,_] _ _ = Bool
  H .Category.id = false
  H .Category._⋆_ = _⊕_
  H .Category.⋆IdL x = refl
  H .Category.⋆IdR = ⊕-identityʳ
  H .Category.⋆Assoc x y z = sym (⊕-assoc x y z)
  H .Category.isSetHom = isSetBool

```

The unique hom-category now has two 2-cells, with exclusive-or as vertical composition. We also want to use exclusive-or horizontally. For that to be functorial, composing the rows of a square of 2-cells and then its columns must give the same result as composing its columns first. Only the middle two terms exchange places, so commutativity and associativity prove interchange.

```agda
  interchange : (a b c d : Bool) → (a ⊕ c) ⊕ (b ⊕ d) ≡ (a ⊕ b) ⊕ (c ⊕ d)
  interchange a b c d = sym (⊕-assoc a c (b ⊕ d))
    ∙ cong (a ⊕_) (⊕-assoc c b d ∙ cong (_⊕ d) (⊕-comm c b) ∙ sym (⊕-assoc b c d))
    ∙ ⊕-assoc a b (c ⊕ d)

  module S = BicategoryStructure

B²Z₂ : Bicategory ℓ-zero ℓ-zero ℓ-zero
B²Z₂ .Bicategory.Ob = Unit
B²Z₂ .Bicategory.hom _ _ = H
B²Z₂ .Bicategory.structure .S.id₁ _ = tt
B²Z₂ .Bicategory.structure .S.comp .Functor.F-ob _ = tt
B²Z₂ .Bicategory.structure .S.comp .Functor.F-hom (α , β) = α ⊕ β
B²Z₂ .Bicategory.structure .S.comp .Functor.F-id = refl
B²Z₂ .Bicategory.structure .S.comp .Functor.F-seq (α , β) (γ , δ) = interchange α β γ δ
B²Z₂ .Bicategory.structure .S.leftUnitor _ = idCatIso
B²Z₂ .Bicategory.structure .S.rightUnitor _ = idCatIso
B²Z₂ .Bicategory.structure .S.associator _ _ _ = idCatIso
B²Z₂ .Bicategory.structure .S.leftUnitor-natural = ⊕-identityʳ
B²Z₂ .Bicategory.structure .S.rightUnitor-natural α = ⊕-identityʳ _ ∙ ⊕-identityʳ α
B²Z₂ .Bicategory.structure .S.associator-natural α β γ = ⊕-identityʳ _ ∙ sym (⊕-assoc α β γ)
B²Z₂ .Bicategory.structure .S.triangle _ _ = refl
B²Z₂ .Bicategory.structure .S.pentagon _ _ _ _ = refl
B²Z₂ .Bicategory.structure .S.unitors-id _ = refl

identity₂ involution₂ : CatIso H tt tt
identity₂ = idCatIso
involution₂ = true , isiso true refl refl

```

What would it mean for a pseudofunctor to identify these two 2-cells? Its functor on the unique hom-category would send $\mathrm{false}$ and $\mathrm{true}$ to the same morphism. A faithful functor reflects that equality, which would force $\mathrm{false}=\mathrm{true}$.

```agda
distinctImages : ∀ {o h c} {D : Bicategory o h c}
  (F : Pseudofunctor B²Z₂ D) → isLocallyWeakEquivalence F
  → ¬ (Pseudofunctor.F₂ F {tt} {tt} {tt} {tt} (fst identity₂)
    ≡ Pseudofunctor.F₂ F {tt} {tt} {tt} {tt} (fst involution₂))
distinctImages F weak p = false≢true
  (isFullyFaithful→Faithful {F = Pseudofunctor.Fₕ F tt tt}
    (isWeakEquivalence.fullfaith (weak tt tt)) tt tt false true p)
```

The completion unit is a weak biequivalence, so its action on 2-cells distinguishes the identity from the involution.

```agda
import Bicategories.RezkCompletion.Construction.Small as Small

private
  unit₂ : Pseudofunctor B²Z₂ (Small.Rezk B²Z₂)
  unit₂ = Small.→Rezk B²Z₂

unitPreservesTwoCells :
  ¬ (Pseudofunctor.F₂ unit₂ {tt} {tt} {tt} {tt} (fst identity₂)
   ≡ Pseudofunctor.F₂ unit₂ {tt} {tt} {tt} {tt} (fst involution₂))
unitPreservesTwoCells = distinctImages {D = Small.Rezk B²Z₂} unit₂ (Small.isWeakBiequivalence→Rezk B²Z₂ .fst)
```
