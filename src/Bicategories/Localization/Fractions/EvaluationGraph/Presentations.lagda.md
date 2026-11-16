# Graph presentations and their comparison cells

Let $J$ send an ordinary functor to the induced functor between completions, and let $\eta_A$ be the ordinary completion unit at $A$. To exhibit $Jf$ as a roof, use the legs $1_A$ and $f$. The presentation still requires a natural isomorphism between the two ways of arriving in the completion of the codomain.

```agda
module Bicategories.Localization.Fractions.EvaluationGraph.Presentations where

open import Cubical.Foundations.Prelude hiding (J)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism using (invFlipSq; isIso→areInv)
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Applications.Categories.CompletionFunctor
import Bicategories.Categories.RezkCompletion as RC
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Inclusion

module Graphs {ℓ p} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RC.RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R G))) where
  open CategoryClass P using (Object)
  private
    module C = Construction (λ (G : Object) → G .fst) R
    module J = Pseudofunctor (Inclusion.smallInclusion P R weak)
    Q = λ (x : Object) → RC.completion (R x)
    η = λ (x : Object) → RC.unit (R x)

```

An `Action` for $f:A\to B$ and $t:QA\to QB$ compares the images of representatives. Evaluate it at the identity isomorphism of each $\eta_A(x)$ and take its inverse. This gives the components of the required label $t\,\eta_A\cong\eta_B f$. Specializing the action gives the labels for a graph, an identity, and a composite.

```agda
  presented : ∀ {A B : Object} {f : Functor (A .fst) (B .fst)} {t : Functor (Q A) (Q B)}
    → C.Action {A} {B} f t → NatIso ((t ∘F η A) ∘F Id) (η B ∘F f)
  presented {A} {B} {f} {t} a .NatIso.trans .NatTrans.N-ob x = a .C.Action.image idCatIso .snd .isIso.inv
  presented {A} {B} {f} {t} a .NatIso.trans .NatTrans.N-hom =
    NatTrans.N-hom (NatIso.trans (symNatIso (C.comparison {A} {B} {f} {t} a)))
  presented a .NatIso.nIso x = invIso (a .C.Action.image idCatIso) .snd

  graph : ∀ {A B : Object} (f : Functor (A .fst) (B .fst))
    → NatIso ((J.F₁ {A} {B} f ∘F η A) ∘F Id) (η B ∘F f)
  graph {A} {B} f = presented {A} {B} (C.action {A = A} {B} f)

  identity : (A : Object) → NatIso ((Id ∘F η A) ∘F Id) (η A ∘F Id)
  identity A = presented {A} {A} (C.identity {A = A})

  composite : ∀ {A B D : Object} (f : Functor (A .fst) (B .fst)) (g : Functor (B .fst) (D .fst))
    → NatIso (((J.F₁ {B} {D} g ∘F J.F₁ {A} {B} f) ∘F η A) ∘F Id) (η D ∘F (g ∘F f))
  composite {A} {B} {D} f g = presented {A} {D}
    (C.composite {A = A} {B} {D} (C.action {A = A} {B} f) (C.action {A = B} {D} g))

```

A 2-cell $\theta:f\Rightarrow g$ must remain compatible with these labels. The square `Boundary.cell` says that evaluating the lifted transformation and then using the target label agrees with using the source label and then applying $\eta_B$ to $\theta_x$. The operation `invFlipSq` changes the orientation of the two isomorphisms from the action.

```agda
  private
    module Boundary {A B : Object} {f g : Functor (A .fst) (B .fst)} {t s : Functor (Q A) (Q B)}
      (a : C.Action {A} {B} f t) (b : C.Action {A} {B} g s) (θ : NatTrans f g) where
      m = C.Cells.liftCell a b θ
      cell : (x : Category.ob (A .fst)) →
        (m ⟦ η A ⟅ x ⟆ ⟧ ⋆⟨ Q B ⟩ (presented {A} {B} b .NatIso.trans ⟦ x ⟧))
        ≡ ((presented {A} {B} a .NatIso.trans ⟦ x ⟧) ⋆⟨ Q B ⟩ η B ⟪ θ ⟦ x ⟧ ⟫)
      cell x = invFlipSq (isIso→areInv (a .C.Action.image idCatIso .snd))
                         (isIso→areInv (b .C.Action.image idCatIso .snd))
                         (C.Cells.preserves a b θ idCatIso)

```

Apply that square to the canonical actions on $f$ and $g$. For `unitCell` and `compCell`, the source transformation is an identity, while the lifted cell is the respective comparison of $J$.

```agda
  cell : ∀ {A B : Object} {f g : Functor (A .fst) (B .fst)} (θ : NatTrans f g)
    (x : Category.ob (A .fst)) →
    (J.F₂ {A} {B} θ ⟦ η A ⟅ x ⟆ ⟧ ⋆⟨ Q B ⟩ (graph {A} {B} g .NatIso.trans ⟦ x ⟧))
    ≡ ((graph {A} {B} f .NatIso.trans ⟦ x ⟧) ⋆⟨ Q B ⟩ η B ⟪ θ ⟦ x ⟧ ⟫)
  cell {A} {B} {f} {g} θ = Boundary.cell (C.action {A = A} {B} f) (C.action {A = A} {B} g) θ

  unitCell : (A : Object) (x : Category.ob (A .fst)) →
    ((J.unit A .fst ⟦ η A ⟅ x ⟆ ⟧) ⋆⟨ Q A ⟩ (graph {A} {A} Id .NatIso.trans ⟦ x ⟧))
    ≡ (identity A .NatIso.trans ⟦ x ⟧ ⋆⟨ Q A ⟩ η A ⟪ Category.id (A .fst) ⟫)
  unitCell A = Boundary.cell (C.identity {A = A}) (C.action {A = A} {A} Id) (idTrans Id)

  compCell : ∀ {A B D : Object} (f : Functor (A .fst) (B .fst))
    (g : Functor (B .fst) (D .fst)) (x : Category.ob (A .fst)) →
    ((J.compositor {A} {B} {D} f g .fst ⟦ η A ⟅ x ⟆ ⟧)
      ⋆⟨ Q D ⟩ (graph {A} {D} (g ∘F f) .NatIso.trans ⟦ x ⟧))
    ≡ ((composite {A} {B} {D} f g .NatIso.trans ⟦ x ⟧) ⋆⟨ Q D ⟩ η D ⟪ Category.id (D .fst) ⟫)
  compCell {A} {B} {D} f g = Boundary.cell
    (C.composite {A = A} {B} {D} (C.action {A = A} {B} f) (C.action {A = B} {D} g))
    (C.action {A = A} {D} (g ∘F f)) (idTrans (g ∘F f))
```
