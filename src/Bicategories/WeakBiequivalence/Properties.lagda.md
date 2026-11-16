# Lifting adjoint equivalences at image objects

Let $F:B\to D$ be weak on each hom-category and suppose both bicategories are locally univalent. We will show that it induces an equivalence between the types of adjoint equivalences $x\simeq y$ and $Fx\simeq Fy$. First write an adjoint equivalence as two opposite arrows, two isomorphisms contracting their composites, and the two triangle equations.

```agda
module Bicategories.WeakBiequivalence.Properties where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_)
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Equiv.Properties using (isEquiv[equivFunA≃B∘f]→isEquiv[f])
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; isoToIsEquiv)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Category.Base hiding (isUnivalent)
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Equivalence.WeakEquivalence as Weak
open import Bicategories.Categories.Isomorphism
open import Bicategories.Base
open import Bicategories.PathReasoning
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Composition
open import Bicategories.Equivalence.Properties
open import Bicategories.Univalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.Pseudofunctor.AdjointEquivalence
open import Bicategories.WeakBiequivalence.Base

private
  module Presentation {o h c} (B : Bicategory o h c) where
    open Bicategory B

    Contraction : ∀ {x y} (f : Cell x y) (g : Cell y x) → Type c
    Contraction {x} f g = CatIso (hom x x) (f ⋆₁ g) (id₁ x)

    Law : ∀ {x y} (f : Cell x y) (g : Cell y x) → Contraction f g → Contraction g f → Type c
    Law f g p q = (associator f g f .fst ⋆₂ (f ◁ q .fst)) ⋆₂ rightUnitor f .fst
                ≡ (p .fst ▷ f) ⋆₂ leftUnitor f .fst

    Diagram : (x y : Ob) → Type (ℓ-max h c)
    Diagram x y = Σ[ f ∈ Cell x y ] Σ[ g ∈ Cell y x ]
                  Σ[ p ∈ Contraction f g ] Σ[ q ∈ Contraction g f ] Law f g p q × Law g f q p

    diagrams : ∀ {x y} → AdjointEquivalence B x y ≃ Diagram x y
    diagrams = isoToEquiv (iso forward backward (λ _ → refl) (λ _ → refl))
      where
      forward : ∀ {x y} → AdjointEquivalence B x y → Diagram x y
      forward (f , d) = f , inverse , invIso unit , counit , triangleL , triangleR
        where open AdjointStructure d
      backward : ∀ {x y} → Diagram x y → AdjointEquivalence B x y
      backward (f , g , p , q , l , r) = f , adj
        where
        adj : AdjointStructure B f
        adj .AdjointStructure.dataOfInverse .InverseData.inverse = g
        adj .AdjointStructure.dataOfInverse .InverseData.unit = invIso p
        adj .AdjointStructure.dataOfInverse .InverseData.counit = q
        adj .AdjointStructure.triangleL = l
        adj .AdjointStructure.triangleR = r


```

The equivalence of diagrams lifts each comparison with the actual action of the pseudofunctor. The comparison for contractions first applies the hom functor and then changes the two endpoints using the compositor and unit. Both triangle identities lie in propositions because 2-cells form sets.

```agda
module _ {o h c o' h' c'} {B : Bicategory o h c} {D : Bicategory o' h' c'}
         (F : Pseudofunctor B D) (uB : isLocallyUnivalent B) (uD : isLocallyUnivalent D)
         (local : isLocallyWeakEquivalence F) where
  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F
    module PB = Presentation B
    module PD = Presentation D
    open isWeakEquivalence

    arrows : ∀ x y → B.Cell x y ≃ D.Cell (F.F₀ x) (F.F₀ y)
    arrows x y = F.F₁ , isEquivF-ob (uB x y) (uD _ _) (local x y)

    contractions : ∀ {x y} (f : B.Cell x y) (g : B.Cell y x)
      → PB.Contraction f g ≃ PD.Contraction (F.F₁ f) (F.F₁ g)
    contractions {x} f g =
      (F-Iso {F = F.Fₕ x x} , isFullyFaithful→isEquivF-Iso {F = F.Fₕ x x} (local x x .fullfaith) _ _)
      ∙ₑ preIsoEquiv (D.hom _ _) (F.compositor f g)
      ∙ₑ postIsoEquiv (D.hom _ _) (invIso (F.unit x))

    triangleEquiv : ∀ {x y} (f : B.Cell x y) (g : B.Cell y x)
      (p : PB.Contraction f g) (q : PB.Contraction g f)
      → PB.Law f g p q ≃ PD.Law (F.F₁ f) (F.F₁ g) (mapContraction F p) (mapContraction F q)
    triangleEquiv {x} {y} f g p q =
      propBiimpl→Equiv (Category.isSetHom (B.hom x y) _ _)
        (Category.isSetHom (D.hom _ _) _ _) preserve
        (reflect (isFullyFaithful→Faithful {F = F.Fₕ x y} (local x y .fullfaith)))
      where open Triangle F f g p q

    liftDiagram : ∀ x y → PB.Diagram x y ≃ PD.Diagram (F.F₀ x) (F.F₀ y)
    liftDiagram x y = Σ-cong-equiv (arrows x y) λ f → Σ-cong-equiv (arrows y x) λ g →
      Σ-cong-equiv (contractions f g) λ p → Σ-cong-equiv (contractions g f) λ q →
      ≃-× (triangleEquiv f g p q) (triangleEquiv g f q p)

  representedAdjointEquivalences : ∀ x y
    → AdjointEquivalence B x y ≃ AdjointEquivalence D (F.F₀ x) (F.F₀ y)
  representedAdjointEquivalences x y = PB.diagrams ∙ₑ liftDiagram x y ∙ₑ invEquiv PD.diagrams

  isEquivMapAdjointEquivalence : ∀ x y → isEquiv (mapAdjointEquivalence F {x} {y})
  isEquivMapAdjointEquivalence x y = representedAdjointEquivalences x y .snd

isWeakBiequivalenceId : ∀ {o h c} (B : Bicategory o h c) → isWeakBiequivalence (idPseudofunctor B)
isWeakBiequivalenceId B .fst x y .isWeakEquivalence.fullfaith f g = idIsEquiv _
isWeakBiequivalenceId B .fst x y .isWeakEquivalence.esssurj f = ∣ f , idCatIso ∣₁
isWeakBiequivalenceId B .snd x = ∣ x , idAdjointEquivalence B x ∣₁
```

For a locally univalent target, the image of the identity adjoint equivalence agrees with the identity through the unit comparison. Adjoint structures on a fixed arrow form a proposition, so path induction extends this computation to every path.

```agda
module _ {o h c o' h' c'} {B : Bicategory o h c} {D : Bicategory o' h' c'}
         (F : Pseudofunctor B D) (uD : isLocallyUnivalent D) where
  private
    module F = Pseudofunctor F

  mapIdAdjointEquivalence : ∀ x → mapAdjointEquivalence F (idAdjointEquivalence B x)
                                 ≡ idAdjointEquivalence D (F.F₀ x)
  mapIdAdjointEquivalence x = Σ≡Prop (isPropAdjointStructure D uD)
    (sym (Cubical.Categories.Category.Base.isUnivalent.CatIsoToPath (uD _ _) (F.unit x)))

  mapPathToAdjointEquivalence : ∀ {x y} (p : x ≡ y)
    → mapAdjointEquivalence F (pathToAdjointEquivalence B p)
    ≡ pathToAdjointEquivalence D (cong F.F₀ p)
  mapPathToAdjointEquivalence {x} = J (λ y p → mapAdjointEquivalence F
    (pathToAdjointEquivalence B p) ≡ pathToAdjointEquivalence D (cong F.F₀ p))
    ( mapAdjointEquivalence F (pathToAdjointEquivalence B (refl {x = x}))
        ≡[ i ]⟨ mapAdjointEquivalence F (pathToAdjointEquivalence-refl B x i) ⟩
      mapAdjointEquivalence F (idAdjointEquivalence B x)
        ≡⟨ mapIdAdjointEquivalence x ⟩
      idAdjointEquivalence D (F.F₀ x)
        ≡⟨ sym (pathToAdjointEquivalence-refl D (F.F₀ x)) ⟩∎
      pathToAdjointEquivalence D (refl {x = F.F₀ x}) )

module _ {o h c o' h' c'} {B : Bicategory o h c} {D : Bicategory o' h' c'}
         (F : Pseudofunctor B D) (uB : isUnivalent B) (uD : isUnivalent D)
         (weak : isWeakBiequivalence F) where
  private
    module F = Pseudofunctor F
```

Now assume that $B$ and $D$ are globally univalent as well, and $F$ is biessentially surjective. The preceding comparison of adjoint equivalences gives an equivalence on object paths, so the object map is an embedding. Biessential surjectivity becomes surjectivity on objects, and a surjective embedding is an equivalence.

```agda
  isEquivObjectMap : isEquiv F.F₀
  isEquivObjectMap = isEmbedding×isSurjection→isEquiv (embedding , surjection)
    where
    embedding : isEmbedding F.F₀
    embedding x y = isEquiv[equivFunA≃B∘f]→isEquiv[f] (cong F.F₀)
      (objectPathEquiv D (uD .snd) _ _)
      (subst isEquiv (funExt (mapPathToAdjointEquivalence F (uD .fst)))
        (compEquiv (objectPathEquiv B (uB .snd) x y)
                   (representedAdjointEquivalences F (uB .fst) (uD .fst) (weak .fst) x y) .snd))
    surjection : isSurjection F.F₀
    surjection y = PT.map (λ (x , e) → x , invEq (objectPathEquiv D (uD .snd) _ _) e)
                          (weak .snd y)
```

Finally, weak biequivalences compose for arbitrary bicategories. Full faithfulness composes on 2-cells. To represent a target arrow or object, first take a representative for the second pseudofunctor and then one for the first, composing the comparisons under truncation.

```agda
isWeakBiequivalenceComp : ∀ {o h c o' h' c' o'' h'' c''}
  {B : Bicategory o h c} {D : Bicategory o' h' c'} {E : Bicategory o'' h'' c''}
  (G : Pseudofunctor D E) (F : Pseudofunctor B D)
  → isWeakBiequivalence G → isWeakBiequivalence F → isWeakBiequivalence (compPseudofunctor G F)
isWeakBiequivalenceComp G F wg wf .fst x y .isWeakEquivalence.fullfaith f g =
  compEquiv (_ , isWeakEquivalence.fullfaith (wf .fst x y) f g)
            (_ , isWeakEquivalence.fullfaith (wg .fst _ _) _ _) .snd
isWeakBiequivalenceComp G F wg wf .fst x y .isWeakEquivalence.esssurj k =
  PT.rec squash₁ (λ (g , α) → PT.map (λ (f , β) →
    f , ⋆Iso (F-Iso {F = Pseudofunctor.Fₕ G _ _} β) α)
    (isWeakEquivalence.esssurj (wf .fst x y) g))
    (isWeakEquivalence.esssurj (wg .fst _ _) k)
isWeakBiequivalenceComp {E = E} G F wg wf .snd z =
  PT.rec squash₁ (λ (y , q) → PT.map (λ (x , p) →
    x , composeAdjointEquivalence E (mapAdjointEquivalence G p) q) (wf .snd y)) (wg .snd z)
```
