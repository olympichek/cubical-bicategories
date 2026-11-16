# Weak biequivalences from pointwise inverse comparisons

Suppose $F:B\to D$ and $G:D\to B$ have pseudonatural transformations $GF\Rightarrow\mathrm{Id}_B$ and $FG\Rightarrow\mathrm{Id}_D$ with equivalences as components. For either composite, its naturality squares identify the hom action followed by whiskering with another whiskering functor. Cancelling that first whiskering shows that the composite is weak on each hom.

```agda
module Bicategories.WeakBiequivalence.PointwiseInverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (iso; isoToIsEquiv)
open import Cubical.Functions.Embedding
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Adjointification
open import Bicategories.Equivalence.Whiskering
open import Bicategories.Equivalence.Whiskering.Right
open import Bicategories.Categories.WeakEquivalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Composition
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.WeakBiequivalence.Base

private
  module _ {a b c} (B : Bicategory a b c) where
    open Bicategory B

    localFromIdentity : (P : Pseudofunctor B B) (α : PseudonaturalTransformation P (idPseudofunctor B))
      → ((x : Ob) → InverseData B (PseudonaturalTransformation.component α x))
      → isLocallyWeakEquivalence P
    localFromIdentity P α e x y =
      weakCancelPost {F = P.Fₕ x y} {G = R} (isWeakEquivalence.fullfaith (rightWhiskerWeakEquivalence B (e y)))
        (weakNatIso (symNatIso n) (leftWhiskerWeakEquivalence B (e x)))
      where
      module P = Pseudofunctor P
      module α = PseudonaturalTransformation α
      R = rightWhisker {x = P.F₀ x} (α.component y)
      L = leftWhisker {z = y} (α.component x)
      n : NatIso (R ∘F P.Fₕ x y) L
      n .NatIso.trans .NatTrans.N-ob f = α.naturality f .fst
      n .NatIso.trans .NatTrans.N-hom = α.naturality₂
      n .NatIso.nIso f = α.naturality f .snd
```

To recover full faithfulness for $F$, consider three consecutive maps on 2-cells, given by $F,G,F$. Each adjacent pair is an equivalence because the corresponding composite hom functor is fully faithful. In general, given maps $f,g,h$ with $gf$ and $hg$ equivalences, $f$ has inverse sending $y$ to $(gf)^{-1}(g(y))$. This gives the required result on 2-cells.

```agda
  firstEquiv : ∀ {a b c d} {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    (f : A → B) (g : B → C) (h : C → D)
    → isEquiv (λ x → g (f x)) → isEquiv (λ x → h (g x)) → isEquiv f
  firstEquiv f g h gf hg = isoToIsEquiv (iso f (λ y → invIsEq gf (g y))
    (λ y → isEmbedding→Inj (isEquiv→isEmbedding hg) _ _ (cong h (secIsEq gf (g y))))
    (retIsEq gf))

  full : ∀ {a b c d e f} {B : Bicategory a b c} {D : Bicategory d e f}
    (F : Pseudofunctor B D) (G : Pseudofunctor D B)
    → isLocallyWeakEquivalence (G ∘P F) → isLocallyWeakEquivalence (F ∘P G)
    → (x y : Bicategory.Ob B) → Functor.isFullyFaithful (Pseudofunctor.Fₕ F x y)
  full F G gf fg x y s t = firstEquiv F.F₂ G.F₂ F.F₂
    (isWeakEquivalence.fullfaith (gf x y) s t)
    (isWeakEquivalence.fullfaith (fg (F.F₀ x) (F.F₀ y)) (F.F₁ s) (F.F₁ t))
    where
    module F = Pseudofunctor F
    module G = Pseudofunctor G
```

Full faithfulness of the two composites makes each hom map fully faithful. Essential surjectivity on 1-cells follows by applying the reverse pseudofunctor to a 1-cell, representing the result along the composite, and lifting the resulting isomorphism through the fully faithful reverse functor.

```agda
module _ {a b c d e f} {B : Bicategory a b c} {D : Bicategory d e f}
  (F : Pseudofunctor B D) (G : Pseudofunctor D B)
  (α : PseudonaturalTransformation (G ∘P F) (idPseudofunctor B))
  (a′ : (x : Bicategory.Ob B) → InverseData B (PseudonaturalTransformation.component α x))
  (β : PseudonaturalTransformation (F ∘P G) (idPseudofunctor D))
  (b′ : (x : Bicategory.Ob D) → InverseData D (PseudonaturalTransformation.component β x)) where
  private
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    gf = localFromIdentity B (G ∘P F) α a′
    fg = localFromIdentity D (F ∘P G) β b′

  inverseComparisons→weak : isWeakBiequivalence F
  inverseComparisons→weak .fst x y .isWeakEquivalence.fullfaith = full F G gf fg x y
  inverseComparisons→weak .fst x y .isWeakEquivalence.esssurj k =
    PT.map (λ (f , e) → f , liftIso {F = G.Fₕ (F.F₀ x) (F.F₀ y)}
      (full G F fg gf _ _) e) (isWeakEquivalence.esssurj (gf x y) (G.F₁ k))
  inverseComparisons→weak .snd z = PT.∣ G.F₀ z , _ , adjointify D (b′ z) ∣₁
```
