# Descending the coherence isomorphisms

Composition has been extended to the completed hom categories. To make it bicategorical we need isomorphisms for composition with identities and for rebracketing a triple composite. We already have both in the bicategory of representatives.

```agda
module Bicategories.RezkCompletion.Local.Coherence where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism using (F-Iso)
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.NaturalTransformation
open import Bicategories.Base
import Bicategories.Categories.RezkCompletion as RC
open import Bicategories.RezkCompletion.Local.Composition
open import Bicategories.RezkCompletion.Local.Restriction

module Coherence {o h c r s} (B : Bicategory o h c)
  (R : (x y : Bicategory.Ob B) → RC.RezkCompletion (Bicategory.hom B x y) r s)
  (weak : ∀ x y → isWeakEquivalence (RC.unit (R x y))) where
  open Operations B R weak
  module T = Bicategory represented
  open Functor
  open NatTrans
  open NatIso

```

Use the image of $1_x$ as the identity of $x$. Write $q$ for the projection that forgets a representative but retains its image in the completed hom. Since $q$ is a weak equivalence, restriction along it lets us recover natural isomorphisms from their values on representatives.

```agda
  I₁ : (x : B.Ob) → Category.ob (H x x)
  I₁ x = η x x ⟅ B.id₁ x ⟆

  qWeak : ∀ x y → isWeakEquivalence (G.second x y)
  qWeak x y = G.secondWeak x y (RC.univalent (R x y)) (weak x y)

```

Fix objects $x,y$. Composing with the chosen identity on the left or right gives the endofunctors $L$ and $R'$ on $H(x,y)$. After restricting along $q$, the original unitors give natural isomorphisms $L\circ q\cong q$ and $R'\circ q\cong q$. Lifting them gives unitors on all of $H(x,y)$. The equations `leftβ` and `rightβ` record their values on a represented arrow.

```agda
  module Units (x y : B.Ob) where
    private
      q = G.second x y
      module Res = Restrict q (qWeak x y) (RC.univalent (R x y))
    L = compose x x y ∘F rinj (H x x) (H x y) (I₁ x)
    R' = compose x y y ∘F linj (H x y) (H y y) (I₁ y)

    left₀ : NatIso (L ∘F q) (Id ∘F q)
    left₀ .trans .N-ob f = q ⟪ T.leftUnitor f .fst ⟫
    left₀ .trans .N-hom α = cong (q ⟪_⟫) (T.leftUnitor-natural α)
    left₀ .nIso f = F-Iso {F = q} (T.leftUnitor f) .snd

    right₀ : NatIso (R' ∘F q) (Id ∘F q)
    right₀ .trans .N-ob f = q ⟪ T.rightUnitor f .fst ⟫
    right₀ .trans .N-hom α = cong (q ⟪_⟫) (T.rightUnitor-natural α)
    right₀ .nIso f = F-Iso {F = q} (T.rightUnitor f) .snd

    opaque
      left : NatIso L Id
      left = Res.liftIso left₀

      right : NatIso R' Id
      right = Res.liftIso right₀

      leftβ : (f : T.Cell x y) → left .trans .N-ob (q ⟅ f ⟆) ≡ q ⟪ T.leftUnitor f .fst ⟫
      leftβ = Res.liftIsoβ {L} {Id} left₀

      rightβ : (f : T.Cell x y) → right .trans .N-ob (q ⟅ f ⟆) ≡ q ⟪ T.rightUnitor f .fst ⟫
      rightβ = Res.liftIsoβ {R'} {Id} right₀

```

For the associator there are three input arrows. Restrict along the product of their three projections. The two bracketings define functors on that product, and the original associator compares them on representatives. Lifting this comparison gives the associator on the completed homs. The equation `assocβ` identifies its components on triples of representatives.

```agda
  module Assoc (w x y z : B.Ob) where
    private
      A = H w x
      C = H x y
      D = H y z
      q = G.second w z
      q₃ = G.second w x ×F (G.second x y ×F G.second y z)
      module Res = Restrict q₃
        (productWeak (qWeak w x) (productWeak (qWeak x y) (qWeak y z)))
        (RC.univalent (R w z))

    L = compose w y z ∘F (compose w x y ×F Id) ∘F ×C-assoc A C D
    R' = compose w x z ∘F (Id ×F compose x y z)

    assoc₀ : NatIso (L ∘F q₃) (R' ∘F q₃)
    assoc₀ .trans .N-ob (f , g , k) = q ⟪ T.associator f g k .fst ⟫
    assoc₀ .trans .N-hom (α , β , γ) = cong (q ⟪_⟫) (T.associator-natural α β γ)
    assoc₀ .nIso (f , g , k) = F-Iso {F = q} (T.associator f g k) .snd

    opaque
      assoc : NatIso L R'
      assoc = Res.liftIso assoc₀

      assocβ : (f : T.Cell w x) (g : T.Cell x y) (k : T.Cell y z)
        → assoc .trans .N-ob (q₃ ⟅ f , g , k ⟆) ≡ q ⟪ T.associator f g k .fst ⟫
      assocβ f g k = Res.liftIsoβ {L} {R'} assoc₀ (f , g , k)
```
