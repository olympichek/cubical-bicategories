# Paths of pseudofunctors into a univalent bicategory

Let $F,G:B\to D$ be pseudofunctors into a univalent bicategory $D$. Given a pseudonatural transformation $\alpha:F\Rightarrow G$ with an adjoint equivalence at each object, we construct a path $F=G$. The proof fixes $F$ and lets the endpoint $G$ vary.

```agda
module Bicategories.Pseudofunctor.Univalence where

open import Cubical.Foundations.Prelude hiding (_▷_; _◁_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path using (symIso)
open import Cubical.Foundations.Isomorphism using (isoToEquiv)
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Categories.Category as Cat hiding (isUnivalent)
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.Compose
open import Cubical.Categories.Functor.ComposeProperty
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Whiskering
open import Bicategories.Univalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Path
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Identity

module _ {o h c r s t} {B : Bicategory o h c} {D : Bicategory r s t}
  (u : isUnivalent D) (F : Pseudofunctor B D) where
  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F
    open D using (_⋆₁_; _⋆₂_; _◁_; _▷_)

```

## Objects and hom functors

For each $x$, consider a possible target $Gx$ together with an adjoint equivalence $Fx\simeq Gx$. Global univalence identifies the type of such pairs with the type of endpoints and paths out of $Fx$. This last type is contractible.

```agda
    Objects = (x : B.Ob) → Σ D.Ob (AdjointEquivalence D (F.F₀ x))
    objectsProp : isProp Objects
    objectsProp = isPropΠ λ x → isContr→isProp (isOfHLevelRespectEquiv 0
      (Σ-cong-equiv-snd (objectPathEquiv D (u .snd) (F.F₀ x))) (isContrSingl _))

```

Fix the objects and the components $\alpha_x$. The naturality isomorphisms for $f:x\to y$ compare $\alpha_y\circ Ff$ with $Gf\circ\alpha_x$. Their right-hand side sees the unknown hom functor only after whiskering by $\alpha_x$. Since this is an adjoint equivalence, whiskering is fully faithful. On the univalent functor categories, postcomposing with that whiskering functor embeds their object types. Each fiber is therefore a proposition, which gives uniqueness of the hom functor together with its naturality isomorphism.

```agda
    module Homs (O : Objects) (x y : B.Ob) where
      X = O x .fst
      Y = O y .fst
      K = D.rightWhisker (O y .snd .fst) ∘F F.Fₕ x y
      W = D.leftWhisker {z = Y} (O x .snd .fst)
      P = postcomposeF (B.hom x y) W

      Data = Σ[ G ∈ Functor (B.hom x y) (D.hom X Y) ] NatIso K (W ∘F G)

      unique : isProp Data
      unique = isOfHLevelRespectEquiv 1
        (Σ-cong-equiv-snd λ G → isoToEquiv symIso ∙ₑ Path≃NatIso (u .fst _ _))
        (isEmbedding→hasPropFibers
          (isFullyFaithful→isEmbd-ob (isUnivalentFUNCTOR _ _ (u .fst _ _))
            (isUnivalentFUNCTOR _ _ (u .fst _ _)) {F = P} fullyFaithful) K)
        where
        fullyFaithful = isFullyFaithfulPostcomposeF {C = B.hom x y} {G = W}
          (isWeakEquivalence.fullfaith
            (leftWhiskerWeakEquivalence D (AdjointStructure.dataOfInverse (O x .snd .snd))))

    HomFamily : Objects → Type _
    HomFamily O = (x y : B.Ob) → Homs.Data O x y

```

## Unit and composition comparisons

With the objects and the hom action fixed, the unit and composition laws for $\alpha$ constrain the remaining comparison cells of $G$. In each equation the unknown cell is whiskered by $\alpha_x$ and composed with a known invertible 2-cell. Cancel the invertible factor, then use faithfulness of whiskering to recover uniqueness of the unknown cell. The lemma `determined` works for both laws.

```agda
    module Comparisons (O : Objects) (H : HomFamily O) where
      g : B.Ob → D.Ob
      g x = O x .fst
      a : (x : B.Ob) → D.Cell (F.F₀ x) (g x)
      a x = O x .snd .fst
      g₁ : ∀ {x y} → B.Cell x y → D.Cell (g x) (g y)
      g₁ {x} {y} f = H x y .fst ⟅ f ⟆
      n : ∀ {x y} (f : B.Cell x y) → CatIso (D.hom (F.F₀ x) (g y))
        (F.F₁ f ⋆₁ a y) (a x ⋆₁ g₁ f)
      n {x} {y} f = H x y .snd .NatIso.trans ⟦ f ⟧ , H x y .snd .NatIso.nIso f

      private
        determined : ∀ {x z} {v w : D.Cell (g x) z} {p : D.Cell (F.F₀ x) z}
          (prefix : CatIso (D.hom _ _) p (a x ⋆₁ v)) (result : D.Two p (a x ⋆₁ w))
          → isProp (Σ[ m ∈ CatIso (D.hom _ _) v w ]
                      result ≡ (prefix .fst ⋆₂ (a x ◁ m .fst)))
        determined {x} {z} prefix result (m , p) (m′ , q) =
          Σ≡Prop (λ _ → Category.isSetHom (D.hom _ _) _ _) (CatIso≡ m m′
            (isFullyFaithful→Faithful {F = D.leftWhisker (a x)} full _ _ _ _
              (⋆CancelL prefix (sym p ∙ q))))
          where
          full = isWeakEquivalence.fullfaith (leftWhiskerWeakEquivalence D {c = z}
            (AdjointStructure.dataOfInverse (O x .snd .snd)))

      unitPrefix : (x : B.Ob) → _
      unitPrefix x = ⋆Iso (D.leftUnitor (a x)) (invIso (D.rightUnitor (a x)))

      UnitAt : B.Ob → Type _
      UnitAt x = Σ[ m ∈ CatIso (D.hom (g x) (g x)) (D.id₁ (g x)) (g₁ (B.id₁ x)) ]
        ((F.unit x .fst ▷ a x) ⋆₂ n (B.id₁ x) .fst) ≡ (unitPrefix x .fst ⋆₂ (a x ◁ m .fst))

      unitsProp : (x : B.Ob) → isProp (UnitAt x)
      unitsProp x = determined {x} (unitPrefix x) _

      compPrefix : ∀ {x y z} (f : B.Cell x y) (k : B.Cell y z) → _
      compPrefix {x} {y} {z} f k =
        ⋆Iso (D.associator (F.F₁ f) (F.F₁ k) (a z))
        (⋆Iso (F-Iso {F = D.leftWhisker (F.F₁ f)} (n k))
        (⋆Iso (invIso (D.associator (F.F₁ f) (a y) (g₁ k)))
        (⋆Iso (F-Iso {F = D.rightWhisker (g₁ k)} (n f)) (D.associator (a x) (g₁ f) (g₁ k)))))

      CompAt : ∀ {x y z} (f : B.Cell x y) (k : B.Cell y z) → Type _
      CompAt {x} {y} {z} f k = Σ[ m ∈ CatIso (D.hom (g x) (g z))
          (g₁ f ⋆₁ g₁ k) (g₁ (f B.⋆₁ k)) ]
        ((F.compositor f k .fst ▷ a z) ⋆₂ n (f B.⋆₁ k) .fst)
        ≡ (compPrefix f k .fst ⋆₂ (a x ◁ m .fst))

      compsProp : ∀ {x y z} (f : B.Cell x y) (k : B.Cell y z) → isProp (CompAt f k)
      compsProp {x} f k = determined {x} (compPrefix f k) _
```

## Recovering the path of pseudofunctors

Package the preceding choices in `Data`. Each stage is a proposition once the earlier choices are fixed, so `uniqueData` proves any two packages equal. An actual endpoint, transformation, and family of adjoint structures give such a package by `readData`. Decoding their equality gives paths in all the data fields, and the remaining coherence proofs agree because they are propositions.

```agda
    Data = Σ[ O ∈ Objects ] Σ[ H ∈ HomFamily O ]
      ((x : B.Ob) → Comparisons.UnitAt O H x)
      × ((x y z : B.Ob) (f : B.Cell x y) (k : B.Cell y z) → Comparisons.CompAt O H f k)

    opaque
      uniqueData : isProp Data
      uniqueData = isPropΣ objectsProp λ O →
        isPropΣ (isPropΠ2 (Homs.unique O)) λ H →
        isProp× (isPropΠ (Comparisons.unitsProp O H))
                (isPropΠ5 λ _ _ _ → Comparisons.compsProp O H)

  Pointed = Σ[ G ∈ Pseudofunctor B D ] Σ[ α ∈ PseudonaturalTransformation F G ]
    ((x : B.Ob) → AdjointStructure D (PseudonaturalTransformation.component α x))

  private
    readData : Pointed → Data
    readData (G , α , e) = O , H , units , comps
      where
      module G = Pseudofunctor G
      module α = PseudonaturalTransformation α
      O : Objects
      O x = G.F₀ x , α.component x , e x
      H : HomFamily O
      H x y .fst = G.Fₕ x y
      H x y .snd .NatIso.trans .NatTrans.N-ob f = α.naturality f .fst
      H x y .snd .NatIso.trans .NatTrans.N-hom = α.naturality₂
      H x y .snd .NatIso.nIso f = α.naturality f .snd
      units : (x : B.Ob) → Comparisons.UnitAt O H x
      units x = G.unit x , α.unitLaw x
      comps : (x y z : B.Ob) (f : B.Cell x y) (k : B.Cell y z) → Comparisons.CompAt O H f k
      comps x y z f k = G.compositor f k , α.compLaw f k

    module Decode (t : Data) where
      O = t .fst
      H = t .snd .fst
      open Comparisons O H using (g; a; n) public
      hom : (x y : B.Ob) → Functor (B.hom x y) (D.hom (g x) (g y))
      hom = λ x y → H x y .fst
      unit : (x : B.Ob) → CatIso (D.hom (g x) (g x)) (D.id₁ (g x)) (hom x x ⟅ B.id₁ x ⟆)
      unit = λ x → t .snd .snd .fst x .fst
      compositor : (x y z : B.Ob) (f : B.Cell x y) (k : B.Cell y z)
        → CatIso (D.hom (g x) (g z)) ((hom x y ⟅ f ⟆) ⋆₁ (hom y z ⟅ k ⟆))
                   (hom x z ⟅ f B.⋆₁ k ⟆)
      compositor = λ x y z f k → t .snd .snd .snd x y z f k .fst

  abstract
    uniquePointed : isProp Pointed
    uniquePointed (G , α , a) (G′ , β , b) = result
      where
      path : readData (G , α , a) ≡ readData (G′ , β , b)
      path = uniqueData (readData (G , α , a)) (readData (G′ , β , b))
      module P (i : I) = Decode (path i)

      functors : G ≡ G′
      functors = pseudofunctorPath {F = G} {G = G′} (λ i → P.g i) (λ i → P.hom i) (λ i → P.unit i)
        (λ i {x} {y} {z} → P.compositor i x y z)

      result : Path Pointed (G , α , a) (G′ , β , b)
      result i .fst = functors i
      result i .snd .fst .PseudonaturalTransformation.component = P.a i
      result i .snd .fst .PseudonaturalTransformation.naturality = P.n i
      result i .snd .fst .PseudonaturalTransformation.laws = isProp→PathP
        (λ j → isPropTransformationLaws F (functors j) (P.a j) (P.n j))
        (PseudonaturalTransformation.laws α) (PseudonaturalTransformation.laws β) i
      result i .snd .snd x = P.O i x .snd .snd

```

The identity transformation of $F$ provides a point of this proposition. It is therefore contractible. The path from that center to $(G,\alpha)$, including the given componentwise adjoint structures, projects to the desired path $F=G$.

```agda
  isContrPointed : isContr Pointed
  isContrPointed = center , uniquePointed center
    where
    center : Pointed
    center = F , identityTransformation F , λ x → idAdjointEquivalence D (F.F₀ x) .snd

transformationToPath : ∀ {o h c r s t} {B : Bicategory o h c} {D : Bicategory r s t}
  (u : isUnivalent D) {F G : Pseudofunctor B D} (α : PseudonaturalTransformation F G)
  → ((x : Bicategory.Ob B) → AdjointStructure D (PseudonaturalTransformation.component α x))
  → F ≡ G
transformationToPath u {F} {G} α e = cong fst (isContrPointed u F .snd (G , α , e))
```
