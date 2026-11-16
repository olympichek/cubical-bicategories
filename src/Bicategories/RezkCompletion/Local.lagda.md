# The local Rezk completion

The first stage of bicategorical Rezk completion keeps the objects of $B$ and replaces each ordinary category $B(x,y)$ by its Rezk completion. How do these independently completed homs fit together, and how does $B$ map into the result?

```agda
module Bicategories.RezkCompletion.Local where

open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Foundations.HLevels using (isPropΠ; isPropΠ2; isPropΠ3)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism using (F-Iso)
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.NaturalTransformation
open import Bicategories.Base
open import Bicategories.Equivalence using (idAdjointEquivalence)
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties using (idPseudofunctor; compPseudofunctor)
open import Bicategories.WeakBiequivalence.Base
import Bicategories.Univalence as Bi
import Bicategories.Categories.RezkCompletion as RC
open import Bicategories.RezkCompletion.Local.Composition
open import Bicategories.RezkCompletion.Local.Coherence
open import Bicategories.RezkCompletion.Local.Structure

private
  module _ {a b c d} {A : Category a b} {D : Category c d} (K : Functor A D) where
    module D = Category D

    prefixId : {x : Category.ob A} {y : D.ob} (α : D [ K ⟅ x ⟆ , y ])
      → ((K ⟪ Category.id A ⟫ D.⋆ D.id) D.⋆ α) ≡ α
    prefixId α = cong (D._⋆ α) (cong (D._⋆ D.id) (Functor.F-id K) ∙ D.⋆IdL _)
      ∙ D.⋆IdL α

    suffixId : {x : D.ob} {y : Category.ob A} (α : D [ x , K ⟅ y ⟆ ])
      → ((α D.⋆ K ⟪ Category.id A ⟫) D.⋆ D.id) ≡ α
    suffixId α = D.⋆IdR _ ∙ cong (α D.⋆_) (Functor.F-id K) ∙ D.⋆IdR α

```

For each pair $x,y$ we are given a completion $R(x,y)$ and a proof that its unit is a weak equivalence. `Structure` has assembled the completed homs into a bicategory. Its construction uses an intermediate bicategory of representatives, where a 1-cell carries both an original 1-cell and its identified image in the completed hom.

```agda
module Local {o h c r s} (B : Bicategory o h c)
  (R : (x y : Bicategory.Ob B) → RC.RezkCompletion (Bicategory.hom B x y) r s)
  (weak : ∀ x y → isWeakEquivalence (RC.unit (R x y))) where
  open Structure B R weak public

  open Operations B R weak
  open Coherence B R weak
```

The unit sends an arrow to its image. On representatives its compositor lies over the identity of the original composite. The first projection checks the pseudofunctor laws there. Projecting to the completed hom-categories and applying the computation rules gives the laws of the unit itself.

```agda
  private
    open Pseudofunctor hiding (unit)
    module IdB = Pseudofunctor (idPseudofunctor B)

    representedUnit : Pseudofunctor B represented
    representedUnit .F₀ x = x
    representedUnit .Fₕ = G.include
    representedUnit .Pseudofunctor.unit x = idCatIso
    representedUnit .compositor {x} {y} {z} f g = G.liftCatIso x z idCatIso
    representedUnit .compositor-natural {x} {y} {z} α β =
      G.arrow≡ x z (IdB.compositor-natural α β)
    representedUnit .leftUnitor-law {x} {y} f = G.arrow≡ x y (IdB.leftUnitor-law f)
    representedUnit .rightUnitor-law {x} {y} f = G.arrow≡ x y (IdB.rightUnitor-law f)
    representedUnit .associator-law {w} {x} {y} {z} f g k =
      G.arrow≡ w z (IdB.associator-law f g k)

```

The second map, `project`, forgets the representative. It respects horizontal composition by construction. The remaining pseudofunctor laws use the computation rules `leftβ`, `rightβ` and `assocβ` for the unitors and associator on represented arrows.

```agda
    module LC = Bicategory completion

    project : Pseudofunctor represented completion
    project .F₀ x = x
    project .Fₕ = G.second
    project .Pseudofunctor.unit x = idCatIso
    project .compositor f g = idCatIso
    project .compositor-natural {x} {y} {z} α β =
      Category.⋆IdR (H x z) (compose x y z ⟪ α .snd .fst , β .snd .fst ⟫)
      ∙ sym (Category.⋆IdL (H x z) (compose x y z ⟪ α .snd .fst , β .snd .fst ⟫))
    project .leftUnitor-law {x} {y} f =
      prefixId (compose x x y) {I₁ x , G.image x y f}
        (T.leftUnitor {x} {y} f .fst .snd .fst) ∙ sym (Units.leftβ x y f)
    project .rightUnitor-law {x} {y} f =
      prefixId (compose x y y) {G.image x y f , I₁ y}
        (T.rightUnitor {x} {y} f .fst .snd .fst) ∙ sym (Units.rightβ x y f)
    project .associator-law {w} {x} {y} {z} f g k =
      prefixId (compose w y z) {(compose w x y ⟅ G.image w x f , G.image x y g ⟆) , G.image y z k}
        (T.associator {w} {x} {y} {z} f g k .fst .snd .fst)
      ∙ sym (Assoc.assocβ w x y z f g k)
      ∙ sym (suffixId (compose w x z) {y = G.image w x f , (compose x y z ⟅ G.image x y g , G.image y z k ⟆)}
        (NatTrans.N-ob (NatIso.trans (Assoc.assoc w x y z))
          (G.image w x f , G.image x y g , G.image y z k)))

```

Compose the two maps to obtain the unit $B\to L B$. On homs it acts as the given ordinary units, so it is locally a weak equivalence. Its object map is the identity, so an object $x$ comes with its own preimage and the identity adjoint equivalence. These are the two parts of `isWeakBiequivalenceUnit`.

```agda
  unit : Pseudofunctor B completion
  unit = compPseudofunctor project representedUnit

  isWeakBiequivalenceUnit : isWeakBiequivalence unit
  isWeakBiequivalenceUnit .fst x y .isWeakEquivalence.fullfaith = isWeakEquivalence.fullfaith (weak x y)
  isWeakBiequivalenceUnit .fst x y .isWeakEquivalence.esssurj = isWeakEquivalence.esssurj (weak x y)
  isWeakBiequivalenceUnit .snd x = PT.∣ x , idAdjointEquivalence completion x ∣₁
```
