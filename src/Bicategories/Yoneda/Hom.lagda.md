# Postcomposition and evaluation on represented homs

For representables $Ya$ and $Yb$, we construct two functors in opposite directions. Postcomposition turns an arrow $a\to b$ into a pseudonatural transformation. Evaluation extracts an arrow from such a transformation.

```agda
module Bicategories.Yoneda.Hom where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_; _◁_▷_)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism using (invFlipSq; isIso→areInv)
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Bicategories.Base
open import Bicategories.Coherence
open import Bicategories.Equivalence.Whiskering
open import Bicategories.Instances.Categories
open import Bicategories.Pseudofunctor.Base
import Bicategories.Univalence as BU

open Functor
open NatTrans
open Pseudofunctor

open import Bicategories.Yoneda.Representable public
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.Modification.Base
open import Bicategories.Modification.Isomorphism

module _ {a b c d e f} {A : Category a b} {B : Category c d} {C : Category e f} where
  whiskerLeftAt : (F : Functor A B) {G G' : Functor B C} (β : NatTrans G G')
    (x : Category.ob A) → whiskerTrans β (idTrans F) ⟦ x ⟧ ≡ β ⟦ F ⟅ x ⟆ ⟧
  whiskerLeftAt F {G} β x = cong (λ v → v ⋆⟨ C ⟩ β ⟦ F ⟅ x ⟆ ⟧) (G .F-id)
    ∙ Category.⋆IdL C _

module _ {o h c} (B : Bicategory o h c) (local : BU.isLocallyUnivalent B) where
  open Bicategory B
  open PseudonaturalTransformation
  open TransformationLaws
  open Modification
  open isIso using (inv)

  private
    Y = representable B local

    assocIso : ∀ {x y a b} (u : Cell x y) (f : Cell a b)
      → CatIso (FUNCTOR (hom y a) (hom x b))
          (rightWhisker f ∘F leftWhisker u) (leftWhisker u ∘F rightWhisker f)
    assocIso u f = NatIso→FUNCTORIso _ _ record
      { trans = natTrans (λ k → associator u k f .fst) (λ α → assocNatM B u α f)
      ; nIso = λ k → associator u k f .snd }

```

For $f:a\to b$, the component at $x$ sends $k:x\to a$ to $f\circ k$. Precomposing $k$ with $u:y\to x$ introduces two ways to parenthesize $f\circ k\circ u$. The associator compares them. Its naturality and the pentagon then give the required laws for `postcompose`.

```agda
  postcompose : ∀ {a b} → Cell a b → PseudonaturalTransformation (Y a) (Y b)
  postcompose f .component x = rightWhisker f
  postcompose f .naturality u = assocIso u f
  postcompose {b = b} f .laws .naturality₂ {y = y} {f = u} {g = v} α =
    makeNatTransPath (funExt λ k →
      cong (_⋆₂ associator v k f .fst) (Category.⋆IdR (hom y b) ((α ▷ k) ▷ f))
      ∙ assocNatR B α k f
      ∙ sym (cong (associator u k f .fst ⋆₂_)
           (whiskerLeftAt (rightWhisker f) (F₂ (Y b) α) k)))
  postcompose {b = b} f .laws .unitLaw x =
    makeNatTransPath (funExt λ k →
      let a = associator (id₁ x) k f
          l = leftUnitor (k ⋆₁ f)
          r = F-Iso {F = rightWhisker f} (leftUnitor k)
          H = hom x b
      in cong (_⋆₂ a .fst) (Category.⋆IdR H (r .snd .inv))
       ∙ sym (⋆InvLMove r (sym (⋆InvRMove l (leftUnitComposite B k f))))
       ∙ sym (cong₂ _⋆₂_ (Category.⋆IdL H (id₂ (k ⋆₁ f)))
              (whiskerLeftAt (rightWhisker f) (Y b .unit x .fst) k)
             ∙ Category.⋆IdL H (l .snd .inv)))
  postcompose {b = b} f .laws .compLaw {z = z} u v =
    makeNatTransPath (funExt λ k →
      let H = hom z b
          p = F-Iso {F = rightWhisker f} (associator v u k)
          q = associator (v ⋆₁ u) k f
          r = associator v u (k ⋆₁ f)
          s = associator v (u ⋆₁ k) f
          t = v ◁ (associator u k f .fst)
          pasting = invFlipSq (isIso→areInv (p .snd)) (isIso→areInv (r .snd)) (pentagon v u k f)
          move₁ = whiskerLeftAt (leftWhisker u) (assocIso v f .fst) k
          move₂ = Category.⋆IdR H t
          move₃ = whiskerLeftAt (rightWhisker f) (Y b .compositor u v .fst) k
      in cong (_⋆₂ q .fst) (Category.⋆IdR H (p .snd .inv))
       ∙ sym pasting
       ∙ sym (cong₂ _⋆₂_
           (Category.⋆IdL H _
            ∙ cong₂ _⋆₂_ move₁ (Category.⋆IdL H _ ∙ Category.⋆IdR H _ ∙ move₂))
           move₃))
```

A 2-cell $\alpha:f\Rightarrow g$ gives a modification whose component at $k$ is $\alpha$ whiskered by $k$. Whiskering is a functor, so it preserves vertical identity and composition, as required for `yonedaHom`.

```agda
  yonedaHom : (a b : Ob) → Functor (hom a b) (transformationCategory (Y a) (Y b))
  yonedaHom a b .F-ob = postcompose
  yonedaHom a b .F-hom α .at x .N-ob k = k ◁ α
  yonedaHom a b .F-hom α .at x .N-hom β = sym (interchange B β α)
  yonedaHom a b .F-hom {f} {g} α .square {y = y} u = makeNatTransPath (funExt λ k →
    cong (_⋆₂ associator u k g .fst)
      (whiskerLeftAt (leftWhisker u) (yonedaHom a b .F-hom α .at y) k)
    ∙ assocNatL B u k α
    ∙ sym (cong (associator u k f .fst ⋆₂_) (Category.⋆IdR (hom y b) (u ◁ (k ◁ α)))))
  yonedaHom a b .F-id = modificationPath (funExt λ x →
    makeNatTransPath (funExt λ k → F-id (leftWhisker k)))
  yonedaHom a b .F-seq α β = modificationPath (funExt λ x →
    makeNatTransPath (funExt λ k → F-seq (leftWhisker k) α β))

```

To read an arrow $a\to b$ back from $T:Ya\Rightarrow Yb$, apply its component at $a$ to $1_a$. For a modification $m$, the corresponding 2-cell is the component of $m_a$ at the same identity.

```agda
  evaluate : (a b : Ob) → Functor (transformationCategory (Y a) (Y b)) (hom a b)
  evaluate a b .F-ob T = T .component a ⟅ id₁ a ⟆
  evaluate a b .F-hom m = m .at a ⟦ id₁ a ⟧
  evaluate a b .F-id = refl
  evaluate a b .F-seq _ _ = refl
```

Why does this one value determine all of $T$? Pseudonaturality for $u:y\to x$ already compares $T_y(k\circ u)$ with $T_x(k)\circ u$. The next definitions extract this isomorphism and the equations it satisfies for 2-cells and composites.

```agda
  module Comparison {a b : Ob} (T : PseudonaturalTransformation (Y a) (Y b)) where
    private
      e = id₁ a
      V = evaluate a b ⟅ T ⟆
      T₀ = component T

      squareIso : ∀ {x y} (u : Cell y x) (k : Cell x a)
        → CatIso (hom y b) (T₀ y ⟅ u ⋆₁ k ⟆) (u ⋆₁ (T₀ x ⟅ k ⟆))
      squareIso u k = T .naturality u .fst ⟦ k ⟧ ,
        FUNCTORIso' _ _ _ (T .naturality u .snd) k

      S : ∀ {x y} (u : Cell y x) (k : Cell x a)
        → Two (T₀ y ⟅ u ⋆₁ k ⟆) (u ⋆₁ (T₀ x ⟅ k ⟆))
      S u k = squareIso u k .fst

      square₂ : ∀ {x y} {u v : Cell y x} (α : Two u v) (k : Cell x a)
        → (T₀ y ⟪ α ▷ k ⟫) ⋆₂ S v k ≡ S u k ⋆₂ (α ▷ (T₀ x ⟅ k ⟆))
      square₂ {x} {y} {u} {v} α k =
        sym (cong (_⋆₂ S v k) (Category.⋆IdR (hom y b) (T₀ y ⟪ α ▷ k ⟫)))
        ∙ cong (_⟦ k ⟧) (T .naturality₂ α)
        ∙ cong (S u k ⋆₂_) (whiskerLeftAt (T₀ x) (F₂ (Y b) α) k)

      squareComp : ∀ {x y z} (u : Cell y x) (v : Cell z y) (k : Cell x a)
        → (T₀ z ⟪ associator v u k .snd .inv ⟫) ⋆₂ S (v ⋆₁ u) k
        ≡ (S v (u ⋆₁ k) ⋆₂ (v ◁ S u k)) ⋆₂ associator v u (T₀ x ⟅ k ⟆) .snd .inv
      squareComp {x} {y} {z} u v k =
        sym (cong (_⋆₂ S (v ⋆₁ u) k) (Category.⋆IdR H (T₀ z ⟪ _ ⟫)))
        ∙ cong (_⟦ k ⟧) (T .compLaw u v)
        ∙ cong₂ _⋆₂_
          (Category.⋆IdL H _
           ∙ cong₂ _⋆₂_ (whiskerLeftAt (leftWhisker u) (T .naturality v .fst) k)
                        (Category.⋆IdL H _ ∙ Category.⋆IdR H _ ∙ Category.⋆IdR H _))
          (whiskerLeftAt (T₀ x) (Y b .compositor u v .fst) k)
        where H = hom z b

```

Set $V=T_a(1_a)$. At $k:x\to a$, the comparison is the following pair of invertible 2-cells. The first inserts an identity using the inverse right unitor in Agda’s composition order. The second is the pseudonaturality square of $T$ for $k$ evaluated at $1_a$.

$$T_x(k)\;\cong\;T_x(1_a\circ k)\;\cong\;T_a(1_a)\circ k.$$

```agda
    compareIso : ∀ {x} (k : Cell x a) → CatIso (hom x b) (T₀ x ⟅ k ⟆) (k ⋆₁ V)
    compareIso {x} k = ⋆Iso (F-Iso {F = T₀ x} (invIso (rightUnitor k))) (squareIso k e)

    private
      natural : ∀ {x} {k l : Cell x a} (α : Two k l)
        → (T₀ x ⟪ α ⟫) ⋆₂ compareIso l .fst ≡ compareIso k .fst ⋆₂ (α ▷ V)
      natural {x} {k} {l} α =
        sym (Category.⋆Assoc H _ _ _)
        ∙ cong (_⋆₂ S l e)
          (sym (F .F-seq α _) ∙ cong (F ⟪_⟫)
            (invFlipSq (isIso→areInv (rightUnitor k .snd))
                       (isIso→areInv (rightUnitor l .snd)) (rightUnitor-natural α))
           ∙ F .F-seq _ (α ▷ e))
        ∙ Category.⋆Assoc H _ _ _
        ∙ cong ((F ⟪ rightUnitor k .snd .inv ⟫) ⋆₂_) (square₂ α e)
        ∙ sym (Category.⋆Assoc H _ _ _)
        where
        F = T₀ x
        H = hom x b
```

To check compatibility with $u:y\to x$, compare the component at $k\circ u$ with the component at $k$ whiskered by $u$. The composition law for $T$ at the pair $u,k$, evaluated at $1_a$, identifies these two pastings after the associators cancel.

```agda
      coherent : ∀ {x y} (u : Cell y x) (k : Cell x a)
        → compareIso (u ⋆₁ k) .fst ⋆₂ associator u k V .fst
        ≡ S u k ⋆₂ (u ◁ compareIso k .fst)
      coherent {x} {y} u k =
        (λ i → (change i ⋆₂ S (u ⋆₁ k) e) ⋆₂ r .fst)
        ∙ cong (_⋆₂ r .fst) (Category.⋆Assoc H _ _ _)
        ∙ Category.⋆Assoc H _ _ _
        ∙ cong ((F ⟪ u ◁ q ⟫) ⋆₂_) cancel
        ∙ sym (Category.⋆Assoc H _ _ _)
        ∙ cong (_⋆₂ (u ◁ S k e)) (T .naturality u .fst .N-hom q)
        ∙ Category.⋆Assoc H _ _ _
        ∙ cong (S u k ⋆₂_) (sym (F-seq (leftWhisker u) (T₀ x ⟪ q ⟫) (S k e)))
        where
        H = hom y b
        F = T₀ y
        q = rightUnitor k .snd .inv
        r = associator u k V
        m = associator u k e
        change = cong (F ⟪_⟫) (sym (cong (λ i → invIso i .fst)
          (CatIso≡ (⋆Iso m (F-Iso {F = leftWhisker u} (rightUnitor k)))
                   (rightUnitor (u ⋆₁ k)) (rightUnitComposite B u k))))
          ∙ F .F-seq (u ◁ q) (m .snd .inv)
        cancel = cong (_⋆₂ r .fst) (squareComp k u e)
          ∙ Category.⋆Assoc H _ _ _
          ∙ cong ((S u (k ⋆₁ e) ⋆₂ (u ◁ S k e)) ⋆₂_) (r .snd .isIso.sec)
          ∙ Category.⋆IdR H _

```

Naturality in $k$ made each component a natural transformation. The equality `coherent` supplies the modification square as $x$ varies. All the component 2-cells are invertible, so these data give an isomorphism in the transformation category.

```agda
    modificationToRepresentable : Modification T (postcompose V)
    modificationToRepresentable .at x = natTrans (λ k → compareIso k .fst) natural
    modificationToRepresentable .square {y = y} u = makeNatTransPath (funExt λ k →
      cong (_⋆₂ associator u k V .fst)
        (whiskerLeftAt (leftWhisker u) (modificationToRepresentable .at y) k)
      ∙ coherent u k
      ∙ sym (cong (S u k ⋆₂_) (Category.⋆IdR (hom y b) (u ◁ compareIso k .fst))))

    comparison : CatIso (transformationCategory (Y a) (Y b)) T (postcompose V)
    comparison = modificationToRepresentable , pointwiseIso modificationToRepresentable
      (λ x → FUNCTORIso _ _ _ (λ k → compareIso k .snd))
```
