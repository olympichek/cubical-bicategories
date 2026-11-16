# Objects with a representative

When we extend composition from a category $C$ to a category $D$ along $J:C\to D$, it is helpful to compute in both at once. This module builds an intermediate category whose objects remember a chosen representative in $C$.

```agda
module Bicategories.RezkCompletion.Local.Representatives where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (iso; isoToIsEquiv)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence.WeakEquivalence

```

A point consists of $a$ in $C$, $d$ in $D$ and a path $J(a)=d$. In `Point`, the singleton type `singl` packages the last two entries. The projections `original` and `image` let us refer to either end of the path `track`.

```agda
module Graph {o h r s} {C : Category o h} {D : Category r s} (J : Functor C D) where
  open Category
  open Functor

  Point : Type (ℓ-max o r)
  Point = Σ[ a ∈ C .ob ] singl (J ⟅ a ⟆)

  original : Point → C .ob
  original = fst

  image : Point → D .ob
  image a = a .snd .fst

  track : (a : Point) → J ⟅ original a ⟆ ≡ image a
  track a = a .snd .snd

```

A morphism likewise remembers $f:a\to b$, a morphism between the specified images and a path relating it to $J(f)$ over the endpoint paths. For fixed $f$ this extra data forms a contractible type. Thus an original morphism lifts by `liftArrow`, and an equality of original morphisms suffices to prove equality upstairs by `arrow≡`.

```agda
  Arrow : Point → Point → Type (ℓ-max h s)
  Arrow a b = Σ[ f ∈ C [ original a , original b ] ]
    singlP (λ i → D [ track a i , track b i ]) (J ⟪ f ⟫)

  arrow≡ : {a b : Point} {α β : Arrow a b} → fst α ≡ fst β → α ≡ β
  arrow≡ {a} {b} = Σ≡Prop λ _ → isPropSinglP

  liftArrow : {a b : Point} → C [ original a , original b ] → Arrow a b
  liftArrow {a} {b} f = f , isContrSinglP _ (J ⟪ f ⟫) .fst

  graph : Category (ℓ-max o r) (ℓ-max h s)
  graph .ob = Point
  graph .Hom[_,_] = Arrow
  graph .id {a} = C .id , D .id , (J .F-id ◁ (λ i → D .id {x = track a i}))
  graph ._⋆_ {x} {y} {z} (f , f' , p) (g , g' , q) =
    f ⋆⟨ C ⟩ g , f' ⋆⟨ D ⟩ g' , (J .F-seq f g ◁ (λ i → p i ⋆⟨ D ⟩ q i))
  graph .⋆IdL α = arrow≡ (C .⋆IdL (fst α))
  graph .⋆IdR α = arrow≡ (C .⋆IdR (fst α))
  graph .⋆Assoc α β γ = arrow≡ (C .⋆Assoc (fst α) (fst β) (fst γ))
  graph .isSetHom = isSetΣ C.isSetHom (λ _ → isProp→isSet isPropSinglP)
    where module C = Category C

```

The resulting category projects to $C$ by taking the original component and to $D$ by taking the specified image. Both projections preserve composition by computation. Every $a$ has a canonical representative $(a,J(a),\mathrm{refl})$, which defines the functor `include`.

```agda
  first : Functor graph C
  first .F-ob = original
  first .F-hom = fst
  first .F-id = refl
  first .F-seq _ _ = refl

  second : Functor graph D
  second .F-ob = image
  second .F-hom α = α .snd .fst
  second .F-id = refl
  second .F-seq _ _ = refl

  include : Functor C graph
  include .F-ob a = a , J ⟅ a ⟆ , refl
  include .F-hom f = f , J ⟪ f ⟫ , refl
  include .F-id = arrow≡ refl
  include .F-seq f g = arrow≡ refl

  private
    abstract
      liftComponent : {a b : Point} (f : C [ original a , original b ])
        → singlP (λ i → D [ track a i , track b i ]) (J ⟪ f ⟫)
      liftComponent f = isContrSinglP _ _ .fst

  liftCatIso : {a b : Point} → CatIso C (original a) (original b) → CatIso graph a b
  liftCatIso α .fst = α .fst , liftComponent (α .fst)
  liftCatIso α .snd .isIso.inv = α .snd .isIso.inv , liftComponent (α .snd .isIso.inv)
  liftCatIso α .snd .isIso.sec = arrow≡ (α .snd .isIso.sec)
  liftCatIso α .snd .isIso.ret = arrow≡ (α .snd .isIso.ret)
```

The first projection forgets a contractible choice of endpoint and path in each hom. On those fibers the second projection acts as the original functor followed by transport. If $J$ is a weak equivalence and $D$ is univalent, every object of $D$ merely has such a representative, so the second projection is weak as well.

```agda
  firstFF : isFullyFaithful first
  firstFF a b = isoToIsEquiv (iso fst liftArrow (λ _ → refl) (λ _ → arrow≡ refl))

  secondWeak : isUnivalent D → isWeakEquivalence J → isWeakEquivalence second
  secondWeak univ w .isWeakEquivalence.fullfaith a b =
    rCancelIsEquiv (F-hom second) (liftArrow {a} {b})
      (compEquiv (_ , isWeakEquivalence.fullfaith w _ _)
        (_ , isEquivTransp (λ i → D [ track a i , track b i ]) i0) .snd)
      (isoToIsEquiv (iso liftArrow fst (λ _ → arrow≡ refl) (λ _ → refl)))
  secondWeak univ w .isWeakEquivalence.esssurj b = PT.map
    (λ (a , p) → (a , b , p) , idCatIso)
    (isSurj→isSurj-ob univ {F = J} (isWeakEquivalence.esssurj w) b)
```
