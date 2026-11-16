# Identities and composites of weak equivalences

A weak equivalence is a fully faithful, essentially surjective functor. For an object $y$ of its target, essential surjectivity gives the mere existence of an $x$ and an isomorphism $Fx\cong y$.

```agda
module Bicategories.Categories.WeakEquivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (isEquiv[equivFunA≃B∘f]→isEquiv[f])
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv)
open import Cubical.Categories.NaturalTransformation
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Equivalence.WeakEquivalence
open isWeakEquivalence

private variable
  o h o' h' o'' h'' : Level

weakId : (C : Category o h) → isWeakEquivalence (𝟙⟨ C ⟩)
weakId C .fullfaith x y = idIsEquiv _
weakId C .esssurj x = PT.∣ x , idCatIso ∣₁

```

For a composite $GF$, compose the hom-set equivalences to prove full faithfulness. For essential surjectivity at $z$, combine witnesses $Gy\cong z$ and $Fx\cong y$ into $GFx\cong z$. The required conclusion is truncated, so both witnesses can be used under truncation.

```agda
weakComposite : {C : Category o h} {D : Category o' h'} {E : Category o'' h''}
              → {F : Functor C D} {G : Functor D E}
              → isWeakEquivalence F → isWeakEquivalence G → isWeakEquivalence (G ∘F F)
weakComposite {F = F} {G} u v .fullfaith =
  isFullyFaithfulG∘F {F = F} {G} (u .fullfaith) (v .fullfaith)
weakComposite {F = F} {G} u v .esssurj z = PT.rec PT.squash₁
  (λ { (y , e) → PT.map (λ { (x , d) → x , ⋆Iso (F-Iso {F = G} d) e }) (u .esssurj y) })
  (v .esssurj z)
```

A natural isomorphism $n:F\cong G$ transfers weak equivalence from $F$ to $G$. Indeed $Gf=n_y\circ Ff\circ n_x^{-1}$, and composition with either isomorphism is an equivalence of hom-sets. The same $n_x^{-1}$ changes a witness $Fx\cong z$ into $Gx\cong z$.

```agda
private
  module _ {C : Category o h} where
    open Category C
    pre : ∀ {x y z} → CatIso C x y → C [ y , z ] ≃ C [ x , z ]
    pre e = isoToEquiv (iso (e .fst ⋆_) (e .snd .isIso.inv ⋆_)
      (λ k → sym (⋆Assoc _ _ _) ∙ cong (_⋆ k) (e .snd .isIso.ret) ∙ ⋆IdL k)
      (λ k → sym (⋆Assoc _ _ _) ∙ cong (_⋆ k) (e .snd .isIso.sec) ∙ ⋆IdL k))

    post : ∀ {x y z} → CatIso C y z → C [ x , y ] ≃ C [ x , z ]
    post e = isoToEquiv (iso (_⋆ e .fst) (_⋆ e .snd .isIso.inv)
      (λ k → ⋆Assoc _ _ _ ∙ cong (k ⋆_) (e .snd .isIso.sec) ∙ ⋆IdR k)
      (λ k → ⋆Assoc _ _ _ ∙ cong (k ⋆_) (e .snd .isIso.ret) ∙ ⋆IdR k))

module _ {C : Category o h} {D : Category o' h'} {F G : Functor C D}
         (n : NatIso F G) (w : isWeakEquivalence F) where
  private
    m : (x : Category.ob C) → CatIso D (F ⟅ x ⟆) (G ⟅ x ⟆)
    m x = n .NatIso.trans ⟦ x ⟧ , n .NatIso.nIso x

  weakNatIso : isWeakEquivalence G
  weakNatIso .fullfaith x y = subst isEquiv (funExt (λ f → sym (NatIso.sqLR n {f = f})))
    (compEquiv (_ , w .fullfaith x y) (compEquiv (pre (invIso (m x))) (post (m y))) .snd)
  weakNatIso .esssurj y = PT.map (λ (x , e) → x , ⋆Iso (invIso (m x)) e) (w .esssurj y)

```

Finally suppose $G$ is fully faithful and $GF$ is a weak equivalence. Cancel the equivalence on each hom-set to get full faithfulness for $F$. For essential surjectivity at $y$, apply the hypothesis to $Gy$ and lift the resulting isomorphism $GFx\cong Gy$ through $G$.

```agda
weakCancelPost : {C : Category o h} {D : Category o' h'} {E : Category o'' h''}
  {F : Functor C D} {G : Functor D E} → Functor.isFullyFaithful G
  → isWeakEquivalence (G ∘F F) → isWeakEquivalence F
weakCancelPost {F = F} {G} ff w .fullfaith x y = isEquiv[equivFunA≃B∘f]→isEquiv[f]
  (Functor.F-hom F) (Functor.F-hom G , ff (F ⟅ x ⟆) (F ⟅ y ⟆)) (w .fullfaith x y)
weakCancelPost {F = F} {G} ff w .esssurj y = PT.map
  (λ (x , e) → x , liftIso {F = G} ff e) (w .esssurj (G ⟅ y ⟆))
```
