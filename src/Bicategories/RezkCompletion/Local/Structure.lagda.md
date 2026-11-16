# Coherence laws for local completion

The remaining step in completing the homs is to prove the bicategory laws for the new composition, unitors and associator. The triangle and pentagon are equalities in hom-sets, so for fixed arrows each is a proposition. This makes it possible to check them on representatives.

```agda
module Bicategories.RezkCompletion.Local.Structure where

open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Foundations.HLevels using (isPropΠ; isPropΠ2; isPropΠ3)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.NaturalTransformation
open import Bicategories.Base
import Bicategories.Univalence as Bi
import Bicategories.Categories.RezkCompletion as RC
open import Bicategories.RezkCompletion.Local.Composition
open import Bicategories.RezkCompletion.Local.Coherence

```

Every arrow $f$ in a completed hom is merely isomorphic to a represented arrow. Univalence of the hom turns that isomorphism into a path. To prove a proposition $P(f)$, we may therefore use a representative, prove $P$ there and transport it along the path. The principle `cases` performs this step for one input at a time.

```agda
module Structure {o h c r s} (B : Bicategory o h c)
  (R : (x y : Bicategory.Ob B) → RC.RezkCompletion (Bicategory.hom B x y) r s)
  (weak : ∀ x y → isWeakEquivalence (RC.unit (R x y))) where
  private
    open Operations B R weak
    open Coherence B R weak
    open NatIso
    open NatTrans
    open BicategoryStructure

    cases : ∀ {k} {x y : B.Ob} {P : Category.ob (H x y) → Type k}
      → (∀ f → isProp (P f)) → (∀ a → P (G.image x y a)) → ∀ f → P f
    cases {x = x} {y} {P} prop rep f = PT.rec (prop f)
      (λ (a , p) → subst P p (rep a)) (covered f)
      where
      covered = isSurj→isSurj-ob (RC.univalent (R x y)) {F = G.second x y}
        (isWeakEquivalence.esssurj (qWeak x y))

    v : ∀ {x y} {f g k : Category.ob (H x y)} → H x y [ f , g ] → H x y [ g , k ]
      → H x y [ f , k ]
    v {x} {y} = Category._⋆_ (H x y)

    ⊗ : ∀ {x y z} {f f' : Category.ob (H x y)} {g g' : Category.ob (H y z)}
      → H x y [ f , f' ] → H y z [ g , g' ]
      → H x z [ compose x y z ⟅ f , g ⟆ , compose x y z ⟅ f' , g' ⟆ ]
    ⊗ {x} {y} {z} α β = compose x y z ⟪ α , β ⟫

```

Use the components of the descended natural isomorphisms for the unitors and associator. Their naturality is already part of those isomorphisms. To check the triangle, apply `cases` to its two inputs, use the computation rules for the descended maps, and project the triangle from the bicategory of representatives. The pentagon uses the same argument on four inputs.

```agda
    localStructure : BicategoryStructure B.Ob H
    localStructure .id₁ = I₁
    localStructure .comp {x} {y} {z} = compose x y z
    localStructure .leftUnitor {x} {y} f =
      Units.left x y .trans .N-ob f , Units.left x y .nIso f
    localStructure .rightUnitor {x} {y} f =
      Units.right x y .trans .N-ob f , Units.right x y .nIso f
    localStructure .associator {w} {x} {y} {z} f g k =
      Assoc.assoc w x y z .trans .N-ob (f , g , k) , Assoc.assoc w x y z .nIso (f , g , k)
    localStructure .leftUnitor-natural {x} {y} α = Units.left x y .trans .N-hom α
    localStructure .rightUnitor-natural {x} {y} α = Units.right x y .trans .N-hom α
    localStructure .associator-natural {w} {x} {y} {z} α β γ =
      Assoc.assoc w x y z .trans .N-hom (α , β , γ)
    localStructure .triangle {x} {y} {z} = cases {x = x} {y} (λ _ → isPropΠ λ _ → setHom _ _)
      (λ f → cases {x = y} {z} (λ _ → setHom _ _) λ g →
        (λ i → v (Assoc.assocβ x y y z f (T.id₁ y) g i)
                  (⊗ (Category.id (H x y)) (Units.leftβ y z g i)))
        ∙ cong (G.second x z ⟪_⟫) (T.triangle f g)
        ∙ (λ i → ⊗ (Units.rightβ x y f (~ i)) (Category.id (H y z))))
      where setHom = λ {a b} → Category.isSetHom (H x z) {a} {b}
    localStructure .pentagon {v₀} {w} {x} {y} {z} = cases {x = v₀} {w}
      (λ _ → isPropΠ3 λ _ _ _ → setHom _ _) (λ f → cases {x = w} {x}
      (λ _ → isPropΠ2 λ _ _ → setHom _ _) (λ g → cases {x = x} {y}
      (λ _ → isPropΠ λ _ → setHom _ _) (λ k → cases {x = y} {z}
      (λ _ → setHom _ _) λ l →
        (λ i → v (Assoc.assocβ v₀ x y z (f T.⋆₁ g) k l i)
                  (Assoc.assocβ v₀ w x z f g (k T.⋆₁ l) i))
        ∙ cong (G.second v₀ z ⟪_⟫) (T.pentagon f g k l)
        ∙ (λ i → v (⊗ (Assoc.assocβ v₀ w x y f g k (~ i)) (Category.id (H y z)))
          (v (Assoc.assocβ v₀ w y z f (g T.⋆₁ k) l (~ i))
             (⊗ (Category.id (H v₀ w)) (Assoc.assocβ w x y z g k l (~ i))))))))
      where setHom = λ {a b} → Category.isSetHom (H v₀ z) {a} {b}
    localStructure .unitors-id x = Units.leftβ x x (T.id₁ x)
      ∙ cong (G.second x x ⟪_⟫) (T.unitors-id x) ∙ sym (Units.rightβ x x (T.id₁ x))

```

These laws finish the bicategory structure on the original objects and the completed homs $H(x,y)$. Its local univalence is exactly the univalence supplied by the chosen ordinary completion of each hom.

```agda
  completion : Bicategory o r s
  completion .Bicategory.Ob = Bicategory.Ob B
  completion .Bicategory.hom = H
  completion .Bicategory.structure = localStructure

  isLocallyUnivalent : Bi.isLocallyUnivalent completion
  isLocallyUnivalent x y = RC.univalent (R x y)
```
