# Comparing units by extension of diagrams

Let $\eta:B\to R$ and $\iota:B\to S$ have univalent targets. We will identify $R$ and $S$ by showing that each unit extends uniquely along the other.

```agda
module Bicategories.RezkCompletion.Comparison.Diagrams where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma
open import Bicategories.Base
open import Bicategories.PathReasoning
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.Pseudofunctor.Composition
open import Bicategories.Univalence
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.WeakBiequivalence.Properties
open import Bicategories.WeakBiequivalence.Inverse
open import Bicategories.StructureIdentity

```

A diagram with values in $E$ is a pseudofunctor into $E$. For a unit $\eta$, `DiagramUniversal` says that restriction $G\mapsto G\circ\eta$ is an equivalence on diagram types for every univalent $E$. Thus any diagram on $B$ has a contractible type of extensions to $R$.

```agda
module _ {a b c d e f} {B : Bicategory a b c} {R : Bicategory d e f}
  (η : Pseudofunctor B R) where

  DiagramUniversal : Typeω
  DiagramUniversal = ∀ {o h k} (E : Bicategory o h k) → isUnivalent E
    → isEquiv (λ (G : Pseudofunctor R E) → G ∘P η)

private
  infixr 25 _⊙_
  opaque
    _⊙_ : ∀ {a b c d e f g h k} {A : Bicategory a b c} {B : Bicategory d e f}
        {C : Bicategory g h k} → Pseudofunctor B C → Pseudofunctor A B → Pseudofunctor A C
    _⊙_ = compPseudofunctor

    computes : ∀ {a b c d e f g h k} {A : Bicategory a b c} {B : Bicategory d e f}
        {C : Bicategory g h k} (G : Pseudofunctor B C) (F : Pseudofunctor A B)
      → G ⊙ F ≡ G ∘P F
    computes G F = refl

  opaque
    unfolding _⊙_
    associative : ∀ {a b c d e f g h k l m n} {A : Bicategory a b c} {B : Bicategory d e f}
        {C : Bicategory g h k} {D : Bicategory l m n}
        (H : Pseudofunctor C D) (G : Pseudofunctor B C) (F : Pseudofunctor A B)
      → H ⊙ (G ⊙ F) ≡ (H ⊙ G) ⊙ F
    associative {A = A} {B} {C} {D} H G F = compAssoc {D = C} {E = D} {B = B} {A = A} H G F

    leftIdentity : ∀ {a b c d e f} {A : Bicategory a b c} {B : Bicategory d e f}
        (F : Pseudofunctor A B) → idPseudofunctor B ⊙ F ≡ F
    leftIdentity {A = A} {B} F = compIdLeft {A = A} {B = B} F

    restriction : ∀ {a b c d e f g h k} {B : Bicategory a b c} {R : Bicategory d e f}
        (η : Pseudofunctor B R) → DiagramUniversal η → (E : Bicategory g h k) → isUnivalent E
      → isEquiv (λ (G : Pseudofunctor R E) → G ⊙ η)
    restriction η r E = r E

```

Apply restriction twice. The center of the fiber over $\iota$ gives a map $U:R\to S$ and a path $U\circ\eta=\iota$. Interchanging the units gives $V:S\to R$ and a path $V\circ\iota=\eta$. In the code these centers are `fwd` and `rev`.

```agda
module Compare {a b c d e f g h k} {B : Bicategory a b c} {R : Bicategory d e f}
  {S : Bicategory g h k} (η : Pseudofunctor B R) (ι : Pseudofunctor B S)
  (u : isUnivalent R) (v : isUnivalent S)
  (restrictionη : DiagramUniversal η) (restrictionι : DiagramUniversal ι) where

  private
    r : ∀ {o h k} (E : Bicategory o h k) → isUnivalent E → isEquiv (λ (G : Pseudofunctor R E) → G ⊙ η)
    r E = restriction η restrictionη E
    s : ∀ {o h k} (E : Bicategory o h k) → isUnivalent E → isEquiv (λ (G : Pseudofunctor S E) → G ⊙ ι)
    s E = restriction ι restrictionι E

    fwd : fiber (λ (G : Pseudofunctor R S) → G ⊙ η) ι
    fwd = r S v .equiv-proof ι .fst

    rev : fiber (λ (G : Pseudofunctor S R) → G ⊙ ι) η
    rev = s R u .equiv-proof η .fst

  forward : Pseudofunctor R S
  forward = fwd .fst

  backward : Pseudofunctor S R
  backward = rev .fst

  forwardUnit : forward ∘P η ≡ ι
  forwardUnit = sym (computes forward η) ∙ fwd .snd

  backwardUnit : backward ∘P ι ≡ η
  backwardUnit = sym (computes backward ι) ∙ rev .snd

```

To see that $V\circ U$ is the identity, restrict it to $B$. There the two unit paths give

$$
(V\circ U)\circ\eta = V\circ(U\circ\eta) = V\circ\iota = \eta.
$$

Both $V\circ U$ and the identity therefore have the same restriction. Since restriction is an equivalence, it reflects this equality. Interchanging $R$ and $S$ proves the other inverse law.

```agda
  retractPath : backward ∘P forward ≡ idPseudofunctor R
  retractPath = sym (computes backward forward) ∙
    isEmbedding→Inj (isEquiv→isEmbedding (r R u)) (backward ⊙ forward) (idPseudofunctor R)
      ( (backward ⊙ forward) ⊙ η
          ≡˘⟨ associative backward forward η ⟩
        backward ⊙ (forward ⊙ η)
          ≡[ j ]⟨ backward ⊙ fwd .snd j ⟩
        backward ⊙ ι
          ≡⟨ rev .snd ⟩
        η ≡⟨ sym (leftIdentity η) ⟩∎ idPseudofunctor R ⊙ η )

  sectionPath : forward ∘P backward ≡ idPseudofunctor S
  sectionPath = sym (computes forward backward) ∙
    isEmbedding→Inj (isEquiv→isEmbedding (s S v)) (forward ⊙ backward) (idPseudofunctor S)
      ( (forward ⊙ backward) ⊙ ι
          ≡˘⟨ associative forward backward ι ⟩
        forward ⊙ (backward ⊙ ι)
          ≡[ j ]⟨ forward ⊙ rev .snd j ⟩
        forward ⊙ η
          ≡⟨ fwd .snd ⟩
        ι ≡⟨ sym (leftIdentity ι) ⟩∎ idPseudofunctor S ⊙ ι )

```

The inverse laws make both comparisons weak biequivalences. They also let us pass that property between the units. If $\iota$ is a weak biequivalence then $V\circ\iota$ is one too, and `backwardUnit` identifies this composite with $\eta$.

```agda
  weakForward : isWeakBiequivalence forward
  weakForward = inverse→isWeakBiequivalence forward backward retractPath sectionPath

  weakBackward : isWeakBiequivalence backward
  weakBackward = inverse→isWeakBiequivalence backward forward sectionPath retractPath

  weakUnit : isWeakBiequivalence ι → isWeakBiequivalence η
  weakUnit weak = subst isWeakBiequivalence backwardUnit
    (isWeakBiequivalenceComp backward ι weakBackward weak)

```

When $R$ and $S$ have the same levels, structure identity turns $U$ into an equality of the targets. Its action on pseudofunctors carries the equation $U\circ\eta=\iota$ to the stated path between the units.

```agda
module _ {a b c d e f} {B : Bicategory a b c} {R S : Bicategory d e f}
  (η : Pseudofunctor B R) (ι : Pseudofunctor B S) (u : isUnivalent R) (v : isUnivalent S)
  (resη : DiagramUniversal η) (resι : DiagramUniversal ι) where
  private module C = Compare η ι u v resη resι

  completionPath : R ≡ S
  completionPath = weakBiequivalence→Path C.forward u v C.weakForward

  completionUnitPath : PathP (λ i → Pseudofunctor B (completionPath i)) η ι
  completionUnitPath = weakBiequivalenceUnitPath C.forward u v C.weakForward η ι C.forwardUnit
```
