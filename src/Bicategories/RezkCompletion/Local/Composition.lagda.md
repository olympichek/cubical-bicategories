# Composition with representatives

Horizontal composition in $B$ is a functor of two variables. Our first task is to define it on two completed hom categories. Our second task is to relate the new composition to the old one precisely enough to carry over the bicategory laws.

```agda
module Bicategories.RezkCompletion.Local.Composition where

open import Cubical.Foundations.Prelude renaming (comp to composePath)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Instances.BinProduct
open import Bicategories.Base
import Bicategories.Categories.RezkCompletion as RC
open import Bicategories.RezkCompletion.Local.Restriction
open import Bicategories.RezkCompletion.Local.Representatives

module Operations {o h c r s} (B : Bicategory o h c)
  (R : (x y : Bicategory.Ob B) → RC.RezkCompletion (Bicategory.hom B x y) r s)
  (weak : ∀ x y → isWeakEquivalence (RC.unit (R x y))) where
  module B = Bicategory B
  open Functor
  open BicategoryStructure

  H : B.Ob → B.Ob → Category r s
  H = λ x y → RC.completion (R x y)
  η : (x y : B.Ob) → Functor (B.hom x y) (H x y)
  η = λ x y → RC.unit (R x y)
  module G (x y : B.Ob) = Graph (η x y)

```

Write $\eta_{xy}:B(x,y)\to H(x,y)$ for each homwise unit. To compose in $H$, first compose in $B$ and apply $\eta_{xz}$ to the result. The product $\eta_{xy}\times\eta_{yz}$ is a weak equivalence, so that functor extends to the completed inputs. The restriction equation `compute` gives, in particular,

$$
\eta_{xz}(g\circ f) = \operatorname{compose}(\eta_{xy}(f),\eta_{yz}(g)).
$$

```agda
  unitProduct : ∀ x y z → Functor (B.hom x y ×C B.hom y z) (H x y ×C H y z)
  unitProduct x y z = η x y ×F η y z

  module Binary (x y z : B.Ob) = Restrict (unitProduct x y z)
    (productWeak (weak x y) (weak y z)) (RC.univalent (R x z))

  opaque
    compose : ∀ x y z → Functor (H x y ×C H y z) (H x z)
    compose x y z = Binary.extend x y z (η x z ∘F B.comp)

    compute : ∀ x y z → η x z ∘F B.comp ≡ compose x y z ∘F unitProduct x y z
    compute x y z = sym (Binary.extendβ x y z (η x z ∘F B.comp))

```

In the graph of the unit we can keep both sides of this equation together. Given representatives of two arrows, `pointTrack` identifies the image of their original composite with the composite of their specified images. For two 2-cells, `arrowTrack` compares their horizontal composites over those same paths. This supplies the object and morphism parts of `graphComp`.

```agda
  graphComp : ∀ x y z → Functor (G.graph x y ×C G.graph y z) (G.graph x z)
  graphComp x y z = op
    where
    S = compose x y z
    abstract
      pointTrack : (a : G.Point x y) (b : G.Point y z)
        → η x z ⟅ (a .fst B.⋆₁ b .fst) ⟆ ≡ S ⟅ G.image x y a , G.image y z b ⟆
      pointTrack a b = cong (λ F → F ⟅ a .fst , b .fst ⟆) (compute x y z)
        ∙ (λ i → S ⟅ G.track x y a i , G.track y z b i ⟆)

      arrowTrack : (a a' : G.Point x y) (b b' : G.Point y z)
        (α : G.Arrow x y a a') (β : G.Arrow y z b b')
        → PathP (λ i → H x z [ pointTrack a b i , pointTrack a' b' i ])
          (η x z ⟪ (α .fst B.⊗ β .fst) ⟫) (S ⟪ α .snd .fst , β .snd .fst ⟫)
      arrowTrack a a' b b' α β i = composePath
        (λ j → H x z [ whole a b j i , whole a' b' j i ])
        (λ j → λ { (i = i0) → η x z ⟪ (α .fst B.⊗ β .fst) ⟫
                 ; (i = i1) → S ⟪ α .snd .snd j , β .snd .snd j ⟫ })
        (compute x y z i ⟪ α .fst , β .fst ⟫)
        where
        whole : (a : G.Point x y) (b : G.Point y z) (j i : I) → Category.ob (H x z)
        whole a b j i = compPath-filler
          (λ i → compute x y z i ⟅ a .fst , b .fst ⟆)
          (λ i → S ⟅ G.track x y a i , G.track y z b i ⟆) j i

    op : Functor (G.graph x y ×C G.graph y z) (G.graph x z)
    op .F-ob (a , b) =
      (a .fst B.⋆₁ b .fst) , S ⟅ G.image x y a , G.image y z b ⟆ , pointTrack a b
    op .F-hom {a , b} {a' , b'} (α , β) = (α .fst B.⊗ β .fst) ,
      S ⟪ α .snd .fst , β .snd .fst ⟫ , arrowTrack a a' b b' α β
    op .F-id = G.arrow≡ x z (B.comp .F-id)
    op .F-seq (α , β) (γ , δ) =
      G.arrow≡ x z (B.comp .F-seq (α .fst , β .fst) (γ .fst , δ .fst))
```

The first projection sends this horizontal functor to the original one on both objects and arrows. It detects equality of morphisms. We can therefore lift the original unitors and associator through it and verify each of their laws in the original bicategory.

```agda
  represented : Bicategory o (ℓ-max h r) (ℓ-max c s)
  represented .Bicategory.Ob = B.Ob
  represented .Bicategory.hom = G.graph
  represented .Bicategory.structure .id₁ x = G.include x x ⟅ B.id₁ x ⟆
  represented .Bicategory.structure .comp {x} {y} {z} = graphComp x y z
  represented .Bicategory.structure .leftUnitor {x} {y} f =
    G.liftCatIso x y (B.leftUnitor (f .fst))
  represented .Bicategory.structure .rightUnitor {x} {y} f =
    G.liftCatIso x y (B.rightUnitor (f .fst))
  represented .Bicategory.structure .associator {w} {x} {y} {z} f g k =
    G.liftCatIso w z (B.associator (f .fst) (g .fst) (k .fst))
  represented .Bicategory.structure .leftUnitor-natural {x} {y} α =
    G.arrow≡ x y (B.leftUnitor-natural (α .fst))
  represented .Bicategory.structure .rightUnitor-natural {x} {y} α =
    G.arrow≡ x y (B.rightUnitor-natural (α .fst))
  represented .Bicategory.structure .associator-natural {w} {x} {y} {z} α β γ =
    G.arrow≡ w z (B.associator-natural (α .fst) (β .fst) (γ .fst))
  represented .Bicategory.structure .triangle {x} {y} {z} f g =
    G.arrow≡ x z (B.triangle (f .fst) (g .fst))
  represented .Bicategory.structure .pentagon {v} {w} {x} {y} {z} f g k l =
    G.arrow≡ v z (B.pentagon (f .fst) (g .fst) (k .fst) (l .fst))
  represented .Bicategory.structure .unitors-id x = G.arrow≡ x x (B.unitors-id x)
```
