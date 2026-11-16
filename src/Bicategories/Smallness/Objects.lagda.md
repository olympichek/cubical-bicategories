# A small carrier from represented path types

Suppose that every point of a type has a mere representative and that paths between represented points have small codes. Replacement constructs an equivalent carrier in the join of the representative and code universes.

```agda
module Bicategories.Smallness.Objects where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Smallness
open import Cubical.Functions.Surjection
import Cubical.HITs.Replacement as Replacement
import Cubical.HITs.PropositionalTruncation as PT
```

Two codes for the same type are equivalent by decoding one and encoding in the other. Univalence identifies their carriers, and the right inverse law identifies their decoding maps over this path. Thus having a small code is a proposition, even when the decoded type lives in a different universe.

```agda
isPropSmall : ∀ {ℓ ℓ'} (T : Type ℓ') → isProp (is[ ℓ ]Small T)
isPropSmall T (A , e) (B , d) = witness
  where
  v = compEquiv e (invEquiv d)
  maps : PathP (λ i → ua v i → T) (e .fst) (d .fst)
  maps = ua→ {e = v} {B = λ _ → T} (λ a → sym (secEq d (e .fst a)))
  witness : (A , e) ≡ (B , d)
  witness i .fst = ua v i
  witness i .snd .fst = maps i
  witness i .snd .snd = isProp→PathP (λ j → isPropIsEquiv (maps j)) (e .snd) (d .snd) i
```

We may now eliminate both mere representatives into the proposition that a path type has a small code. Replacement embeds its carrier into the original type. The representative of each point also witnesses surjectivity of this embedding.

```agda
module Image {ℓOb ℓPath ℓX} {A : Type ℓOb} {X : Type ℓX}
  (j : A → X) (onto : isSurjection j)
  (paths : (a b : A) → is[ ℓPath ]Small (j a ≡ j b)) where

  locallySmall : isLocally[ ℓPath ]Small X
  locallySmall x y = PT.rec2 (isPropSmall (x ≡ y))
    (λ { (a , p) (b , q) → subst2 (λ z w → is[ _ ]Small (z ≡ w)) p q (paths a b) })
    (onto x) (onto y)

  private
    relation = locallySmall→UARel locallySmall

```

We can now factor the given surjection $j:A\to X$ as
$$
A \xrightarrow{\mathrm{include}} \mathrm{Carrier}
  \xrightarrow[\simeq]{\mathrm{decode}} X .
$$
The advantage of the middle type is its universe bound. Only the size of $A$ and the size of the path codes enter. Replacement supplies an embedding into $X$, and `onto` shows that every point lies in its image. The last line checks that decoding an included representative gives back $j(a)$.

```agda
  Carrier : Type (ℓ-max ℓOb ℓPath)
  Carrier = Replacement.Replacement relation j

  include : A → Carrier
  include = Replacement.rep

  decode : Carrier ≃ X
  decode .fst = Replacement.unrep relation j
  decode .snd = isEmbedding×isSurjection→isEquiv
    (Replacement.isEmbeddingUnrep relation j ,
     λ x → PT.map (λ { (a , p) → include a , p }) (onto x))

  decodeInclude : (a : A) → decode .fst (include a) ≡ j a
  decodeInclude a = refl
```
