# Propagating the composite law along three arrows

The composition law for a family of squares $s$ asserts that pasting $s(f),s(g)$ gives $s(f\star g)$. When three arrows $w,f,g$ occur together we can deduce one such law from the others.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.Transformations.ThreeArrows where

open import Cubical.Foundations.Prelude hiding (Square; comp)
open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Functions.Embedding
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.Localization.Fractions.Naturality using (module Cancel)
open import Bicategories.Localization.Fractions.Transformations.Cells using (module Relations)
open import Bicategories.Localization.Fractions.Transformations.Pasting

module CompositeLaws {o h c i j k} {L : Bicategory o h c} {D : Bicategory i j k}
  (F G : Pseudofunctor L D) (x : Component F G) (s : Naturality F G x)
  (isoLaw : ∀ {a b} {f g : Bicategory.Cell L a b} (e : CatIso (Bicategory.hom L a b) f g)
    → Relations.Over F G (x a) (x b) (e .fst) (s f) (s g)) where
  private
    module L = Bicategory L
    module D = Bicategory D
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    open Cancel F G using (Square; pasteSquares)

    sq : ∀ {a b} (f : L.Cell a b) → Type _
    sq {a} {b} = Square (x a) (x b)

  paste : ∀ {a b c} (f : L.Cell a b) (g : L.Cell b c) → sq f → sq g → sq (f L.⋆₁ g)
  paste {a} {b} {c} f g = pasteSquares f g (x a) (x b) (x c)

  Law : ∀ {a b c} → L.Cell a b → L.Cell b c → Type _
  Law f g = paste f g (s f) (s g) ≡ s (f L.⋆₁ g)

```

Put $u=w\star f$ and $v=f\star g$, composing from left to right. The triple paste grouped on the left lies over $u\star g$, while the one grouped on the right lies over $w\star v$. Both the pasted squares and the chosen family respect the isomorphism between these arrows.

```agda
  module Three {a b c d} (w : L.Cell a b) (f : L.Cell b c) (g : L.Cell c d) where
    private
      u = w L.⋆₁ f
      v = f L.⋆₁ g
      A = L.associator w f g
      left = paste u g (paste w f (s w) (s f)) (s g)
      right = paste w v (s w) (paste f g (s f) (s g))
      m = pasteAssociator F G w f g (x a) (x b) (x c) (x d) (s w) (s f) (s g)
      n = isoLaw A
      P = F-Iso {F = D.rightWhisker (x d)} (F-Iso {F = F.Fₕ a d} A)
      Q = F-Iso {F = D.leftWhisker (x a)} (F-Iso {F = G.Fₕ a d} A)

```

The two rectangles over the associator let us pass an equality of squares from one parenthesization to the other. Cancel the whiskered image of the associator on the appropriate side.

```agda
      opaque
        fromLeft : left ≡ s (u L.⋆₁ g) → right ≡ s (w L.⋆₁ v)
        fromLeft p = CatIso≡ _ _ (⋆CancelL P
          (m ∙ cong (λ r → r D.⋆₂ Q .fst) (cong fst p) ∙ sym n))

        fromRight : right ≡ s (w L.⋆₁ v) → left ≡ s (u L.⋆₁ g)
        fromRight p = CatIso≡ _ _ (⋆CancelR Q
          (sym m ∙ cong (P .fst D.⋆₂_) (cong fst p) ∙ n))

```

If the laws for $(w,f),(f,g),(w,v)$ hold, regrouping gives the law for $(u,g)$. In the opposite direction we want to recover the law for $(f,g)$ itself. When $F(w)$ is an equivalence, pasting by $s(w)$ is injective, so we can remove that common prefix.

```agda
    opaque
      leftLaw : Law w f → Law f g → Law w v → Law u g
      leftLaw wf fg wv = sym (cong (λ n → paste u g n (s g)) wf)
        ∙ fromRight (cong (paste w v (s w)) fg ∙ wv)

      cancelPrefix : InverseData D (F.F₁ w) → Law w f → Law u g → Law w v → Law f g
      cancelPrefix inv wf ug wv =
        isEmbedding→Inj (isEquiv→isEmbedding
          (Cancel.Along.isEquivPaste F G w v inv (x a) (x b) (x d) (s w))) _ _
          (fromLeft (cong (λ n → paste u g n (s g)) wf ∙ ug) ∙ sym wv)
```
