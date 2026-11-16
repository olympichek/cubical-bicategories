# Whiskering by an equivalence

Given $f:a\to b$, composition on the left defines a functor $L_f:B(b,c)\to B(a,c)$ with $L_f(h)=f\star h$. If $g$ is an inverse to $f$, the candidate inverse functor is $L_g$. We build the two natural isomorphisms that witness this.

```agda
module Bicategories.Equivalence.Whiskering where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_; _◁_▷_; comp)
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.Base using (WeakInverse)
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.PathReasoning
open import Bicategories.Equivalence

module _ {ℓOb ℓ₁ ℓ₂} (B : Bicategory ℓOb ℓ₁ ℓ₂) where
  open Bicategory B

  interchange : ∀ {a b c} {f f' : Cell a b} {g g' : Cell b c} (α : Two f f') (β : Two g g')
    → (f ◁ β) ⋆₂ (α ▷ g') ≡ (α ▷ g) ⋆₂ (f' ◁ β)
  interchange {a} {b} {c} {f} {f'} {g} {g'} α β =
    (f ◁ β) ⋆₂ (α ▷ g')
      ≡˘⟨ Functor.F-seq comp (id₂ f , β) (α , id₂ g') ⟩
    (id₂ f ⋆₂ α) ⊗ (β ⋆₂ id₂ g')
      ≡[ i ]⟨ Category.⋆IdL (hom a b) α i ⊗ Category.⋆IdR (hom b c) β i ⟩
    α ⊗ β
      ≡[ i ]⟨ Category.⋆IdR (hom a b) α (~ i) ⊗ Category.⋆IdL (hom b c) β (~ i) ⟩
    (α ⋆₂ id₂ f') ⊗ (id₂ g ⋆₂ β)
      ≡⟨ Functor.F-seq comp (α , id₂ g) (id₂ f' , β) ⟩∎
    (α ▷ g) ⋆₂ (f' ◁ β)
```

The associator compares $L_{f\star g}$ with $L_f\circ L_g$, and the left unitor compares $L_1$ with the identity functor. An invertible 2-cell between two choices of $f$ gives an isomorphism of whiskering functors. Its naturality is precisely the interchange identity above.

```agda
  leftWhiskerAssociator : ∀ {a b c d} (f : Cell a b) (g : Cell b c)
    → NatIso (leftWhisker {z = d} (f ⋆₁ g)) (leftWhisker f ∘F leftWhisker g)
  leftWhiskerAssociator f g .NatIso.trans .NatTrans.N-ob h = associator f g h .fst
  leftWhiskerAssociator f g .NatIso.nIso h = associator f g h .snd
  leftWhiskerAssociator f g .NatIso.trans .NatTrans.N-hom {h} {h'} α =
    cong (λ u → (u ⊗ α) ⋆₂ associator f g h' .fst) (sym (Functor.F-id comp))
    ∙ associator-natural (id₂ f) (id₂ g) α

  leftWhiskerUnitor : ∀ {a b} → NatIso (leftWhisker {z = b} (id₁ a)) Id
  leftWhiskerUnitor .NatIso.trans .NatTrans.N-ob h = leftUnitor h .fst
  leftWhiskerUnitor .NatIso.trans .NatTrans.N-hom = leftUnitor-natural
  leftWhiskerUnitor .NatIso.nIso h = leftUnitor h .snd

  changingLeftWhisker : ∀ {a b c} {f g : Cell a b} → CatIso (hom a b) f g
                       → NatIso (leftWhisker {z = c} f) (leftWhisker g)
  changingLeftWhisker p .NatIso.trans .NatTrans.N-ob h = p .fst ▷ h
  changingLeftWhisker p .NatIso.trans .NatTrans.N-hom α = interchange (p .fst) α
  changingLeftWhisker p .NatIso.nIso h = F-Iso {F = rightWhisker h} p .snd
```

Apply these comparisons to the unit and counit of the given inverse. They give $L_f\circ L_g\cong\mathrm{Id}$ and $L_g\circ L_f\cong\mathrm{Id}$. A functor with such a weak inverse is a weak equivalence of categories.

```agda
  leftWhiskerWeakInverse : ∀ {a b c} {f : Cell a b} → InverseData B f
                         → WeakInverse (leftWhisker {z = c} f)
  leftWhiskerWeakInverse d .WeakInverse.invFunc = leftWhisker (InverseData.inverse d)
  leftWhiskerWeakInverse {f = f} d .WeakInverse.η =
    symNatIso (seqNatIso (symNatIso (leftWhiskerAssociator (InverseData.inverse d) f))
      (seqNatIso (changingLeftWhisker (InverseData.counit d)) leftWhiskerUnitor))
  leftWhiskerWeakInverse {f = f} d .WeakInverse.ε =
    seqNatIso (symNatIso (leftWhiskerAssociator f (InverseData.inverse d)))
      (seqNatIso (changingLeftWhisker (invIso (InverseData.unit d))) leftWhiskerUnitor)

  leftWhiskerWeakEquivalence : ∀ {a b c} {f : Cell a b} → InverseData B f
                             → isWeakEquivalence (leftWhisker {z = c} f)
  leftWhiskerWeakEquivalence d = isEquiv→isWeakEquiv ∣ leftWhiskerWeakInverse d ∣₁
```
