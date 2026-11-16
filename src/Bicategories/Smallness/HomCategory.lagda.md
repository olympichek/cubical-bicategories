# Small codes for a category

Object and morphism codes can live in two independent universes. A fully faithful functor from a small category supplies both codes when its object map is an equivalence.

```agda
module Bicategories.Smallness.HomCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Smallness
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism using (F-Iso; F-pathToIso-∘)
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
import Cubical.HITs.PropositionalTruncation as PT

open import Bicategories.Smallness.Objects using (isPropSmall)
open import Bicategories.PathReasoning using (last-step)

open Functor using (isFullyFaithful)

Sized : ∀ ℓOb ℓHom {r s} → Category r s → Type _
Sized ℓOb ℓHom C = Σ (is[ ℓOb ]Small (Category.ob C)) λ _ →
  (f g : Category.ob C) → is[ ℓHom ]Small (C [ f , g ])

isPropSized : ∀ {r s} ℓOb ℓHom (C : Category r s) → isProp (Sized ℓOb ℓHom C)
isPropSized _ _ C = isPropΣ (isPropSmall _) λ _ → isPropΠ2 λ _ _ → isPropSmall _

module _ {o h r s} {D : Category o h} {C : Category r s} (F : Functor D C)
  (objects : isEquiv (Functor.F-ob F)) (homs : isFullyFaithful F) where

  private
    e : Category.ob D ≃ Category.ob C
    e = Functor.F-ob F , objects

```

For a fully faithful functor whose object map is an equivalence, the source supplies these codes. For target objects $x,y$, take their inverse images under the object equivalence. Full faithfulness identifies the source hom between those objects with the target hom, after transporting its endpoints to $x$ and $y$.

```agda
  representedSize : Sized o h C
  representedSize .fst = Category.ob D , e
  representedSize .snd x y = subst2 (λ a b → is[ h ]Small (C [ a , b ]))
    (secEq e x) (secEq e y)
    ((D [ invEq e x , invEq e y ]) , Functor.F-hom F , homs _ _)
```

The comparison decodes each object and arrow. Encoding the identity and the composite of decoded arrows gives the small category's operations. The section law removes intermediate encodings in the category laws.

```agda
module Resize {o h r s} (C : Category r s) (size : Sized o h C) where
  open Category

  objects = size .fst .snd

  private
    module C = Category C

    m : ∀ x y → _
    m x y = size .snd (objects .fst x) (objects .fst y) .snd

  small : Category o h
  small .ob = size .fst .fst
  small .Hom[_,_] x y = size .snd (objects .fst x) (objects .fst y) .fst
  small .id {x} = invEq (m x x) (C .id)
  small ._⋆_ {x} {y} {z} f g = invEq (m x z) (C ._⋆_ (m x y .fst f) (m y z .fst g))
```

Look at the left identity law. After decoding, the new identity is the encoding of the old identity followed by decoding, which cancels by `secEq`. The original category’s left identity law now applies. Re-encoding the answer and using `retEq` gives back the original coded arrow. The associativity calculation below performs the same cancellation on an intermediate composite.

```agda
  small .⋆IdL {x} {y} f = cong (invEq (m x y))
    (m x x .fst (invEq (m x x) C.id) C.⋆ f′
       ≡[ i ]⟨ secEq (m x x) C.id i C.⋆ f′ ⟩
     C.id C.⋆ f′ ≡⟨ C.⋆IdL f′ ⟩∎ f′)
    ∙ retEq (m x y) f
    where f′ = m x y .fst f
  small .⋆IdR {x} {y} f = cong (invEq (m x y))
    (f′ C.⋆ m y y .fst (invEq (m y y) C.id)
       ≡[ i ]⟨ f′ C.⋆ secEq (m y y) C.id i ⟩
     f′ C.⋆ C.id ≡⟨ C.⋆IdR f′ ⟩∎ f′)
    ∙ retEq (m x y) f
    where f′ = m x y .fst f
  small .⋆Assoc {x} {y} {z} {w} f g k = cong (invEq (m x w))
    (m x z .fst (invEq (m x z) (f′ C.⋆ g′)) C.⋆ k′
       ≡[ i ]⟨ secEq (m x z) (f′ C.⋆ g′) i C.⋆ k′ ⟩
     (f′ C.⋆ g′) C.⋆ k′ ≡⟨ C.⋆Assoc f′ g′ k′ ⟩
     f′ C.⋆ (g′ C.⋆ k′)
       ≡⟨ (λ i → f′ C.⋆ secEq (m y w) (g′ C.⋆ k′) (~ i)) ⟩∎
     f′ C.⋆ m y w .fst (invEq (m y w) (g′ C.⋆ k′)))
    where
    f′ = m x y .fst f
    g′ = m y z .fst g
    k′ = m z w .fst k
  small .isSetHom {x} {y} = isOfHLevelRespectEquiv 2 (invEquiv (m x y)) (C .isSetHom)

  comparison : Functor small C
  comparison .Functor.F-ob = objects .fst
  comparison .Functor.F-hom {x} {y} = m x y .fst
  comparison .Functor.F-id {x} = secEq (m x x) _
  comparison .Functor.F-seq {x} {y} {z} f g = secEq (m x z) _

  fullyFaithful : isFullyFaithful comparison
  fullyFaithful x y = m x y .snd

  weakComparison : isWeakEquivalence comparison
  weakComparison .isWeakEquivalence.fullfaith = fullyFaithful
  weakComparison .isWeakEquivalence.esssurj =
    isSurj-ob→isSurj {F = comparison} (isEquiv→isSurjection (objects .snd))

  univalent : isUnivalent C → isUnivalent small
  univalent u .isUnivalent.univ x y = isEquiv[equivFunA≃B∘f]→isEquiv[f] _
    (_ , isFullyFaithful→isEquivF-Iso {F = comparison} fullyFaithful x y)
    (subst isEquiv (sym (F-pathToIso-∘ {F = comparison}))
      (compEquiv (_ , isEquiv→isEmbedding (objects .snd) x y) (_ , u .isUnivalent.univ _ _) .snd))
```

For a family of hom-categories, both smallness conditions are propositions. Thus codes at represented objects suffice to resize every hom, without choosing a representative for either endpoint.

```agda
module Descent {o d a c h k} {A : Type o} {X : Type d} (j : A → X)
  (onto : isSurjection j) (H : X → X → Category a c)
  (atPoints : (u v : A) → Sized h k (H (j u) (j v))) where

  sizes : (x y : X) → Sized h k (H x y)
  sizes x y = PT.rec2 (isPropSized h k (H x y))
    (λ { (u , p) (v , q) → subst2 (λ x y → Sized h k (H x y)) p q (atPoints u v) })
    (onto x) (onto y)

  module Hom (x y : X) = Resize (H x y) (sizes x y)
```
