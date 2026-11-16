# The bicategory of categories

An object of $\mathrm{Cat}$ is an ordinary category $C$. For $C,D$, its hom-category is $\operatorname{Fun}(C,D)$, with natural transformations as arrows. To define horizontal composition of transformations, evaluate a composable pair of functors and arrows. Functoriality of evaluation gives interchange.

```agda
module Bicategories.Instances.Categories where

open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.BinProduct

private
  variable
    ℓOb ℓHom : Level
    A B C D : Category ℓOb ℓHom

open Functor
open Category
open NatTrans

composeFunctors : Functor (FUNCTOR A B ×C FUNCTOR B C) (FUNCTOR A C)
composeFunctors .F-ob (F , G) = G ∘F F
composeFunctors .F-hom (α , β) = whiskerTrans β α
composeFunctors {B = B} {C = C} .F-id {F , G} =
  makeNatTransPath (funExt λ x → appF B C .F-id {G , F ⟅ x ⟆})
composeFunctors {B = B} {C = C} .F-seq (α , β) (α' , β') =
  makeNatTransPath (funExt λ x → appF B C .F-seq (β , α ⟦ x ⟧) (β' , α' ⟦ x ⟧))
```

The unitors and associator have identity components. Their source and target functors agree on objects and arrows, so naturality at each arrow is the identity square.

```agda
private
  fromComponents : {F G : Functor A B}
                 → (e : (x : A .ob) → CatIso B (F ⟅ x ⟆) (G ⟅ x ⟆))
                 → N-hom-Type F G (λ x → e x .fst)
                 → CatIso (FUNCTOR A B) F G
  fromComponents {A = A} {B = B} e natural =
    NatIso→FUNCTORIso A B record
      { trans = natTrans (λ x → e x .fst) natural
      ; nIso = λ x → e x .snd
      }

  idSquare : (C : Category ℓOb ℓHom) {x y : C .ob} (f : C [ x , y ])
           → f ⋆⟨ C ⟩ C .id ≡ C .id ⋆⟨ C ⟩ f
  idSquare C f = C .⋆IdR f ∙ sym (C .⋆IdL f)

  leftId : (F : Functor A B) → CatIso (FUNCTOR A B) (F ∘F Id) F
  leftId {B = B} F = fromComponents (λ _ → idCatIso) λ f → idSquare B (F ⟪ f ⟫)

  rightId : (F : Functor A B) → CatIso (FUNCTOR A B) (Id ∘F F) F
  rightId {B = B} F = fromComponents (λ _ → idCatIso) λ f → idSquare B (F ⟪ f ⟫)

  reassociate : (F : Functor A B) (G : Functor B C) (H : Functor C D)
              → CatIso (FUNCTOR A D) (H ∘F (G ∘F F)) ((H ∘F G) ∘F F)
  reassociate {D = D} F G H =
    fromComponents (λ _ → idCatIso) λ f → idSquare D (H ⟪ G ⟪ F ⟪ f ⟫ ⟫ ⟫)
```

```agda
open import Bicategories.Base
open import Bicategories.FullSubbicategory

open Bicategory

CATAt : (o h : Level) → Bicategory (ℓ-suc (ℓ-max o h)) (ℓ-max o h) (ℓ-max o h)
CATAt o h .Ob = Category o h
CATAt o h .hom = FUNCTOR
CATAt o h .structure .BicategoryStructure.id₁ = 𝟙⟨_⟩
CATAt o h .structure .BicategoryStructure.comp = composeFunctors
CATAt o h .structure .BicategoryStructure.leftUnitor = leftId
CATAt o h .structure .BicategoryStructure.rightUnitor = rightId
CATAt o h .structure .BicategoryStructure.associator = reassociate
CATAt o h .structure .BicategoryStructure.leftUnitor-natural {y = B} {f = F} α =
  makeNatTransPath (funExt λ x →
    B .⋆IdR _ ∙ cong (λ f → f ⋆⟨ B ⟩ α ⟦ x ⟧) (F .F-id))
CATAt o h .structure .BicategoryStructure.rightUnitor-natural {y = B} α =
  makeNatTransPath (funExt λ x →
    B .⋆IdR _ ∙ B .⋆IdR _ ∙ sym (B .⋆IdL _))
CATAt o h .structure .BicategoryStructure.associator-natural {z = D} {h = H} α β γ =
  makeNatTransPath (funExt λ x →
    D .⋆IdR _ ∙ cong (λ f → f ⋆⟨ D ⟩ γ ⟦ _ ⟧) (H .F-seq _ _)
    ∙ D .⋆Assoc _ _ _ ∙ sym (D .⋆IdL _))
CATAt o h .structure .BicategoryStructure.triangle {z = C} F G =
  makeNatTransPath (funExt λ x → C .⋆IdL _)
CATAt o h .structure .BicategoryStructure.pentagon {z = D} F G H K =
  makeNatTransPath (funExt λ x →
    D .⋆IdL _ ∙ sym
      (cong₂ (D ._⋆_) (cong (λ f → f ⋆⟨ D ⟩ D .id) (K .F-id) ∙ D .⋆IdL _)
        (D .⋆IdL _ ∙ cong (λ f → f ⋆⟨ D ⟩ D .id) ((K ∘F H ∘F G) .F-id)
                   ∙ D .⋆IdL _)
       ∙ D .⋆IdL _))
CATAt o h .structure .BicategoryStructure.unitors-id A = makeNatTransPath refl

```

At equal object and hom levels we write $\mathrm{CAT}$. Two full subbicategories keep the same functors and transformations but restrict objects. In $\mathrm{STRICTCAT}$ the objects of each category form a set. In $\mathrm{UNIVCAT}$ the map $(x=y)\to(x\cong y)$ is an equivalence in each category. Functor categories inherit univalence from a univalent codomain.

```agda
CAT : (ℓ : Level) → Bicategory (ℓ-suc ℓ) ℓ ℓ
CAT ℓ = CATAt ℓ ℓ

UNIVCATAt : (o h : Level) → Bicategory (ℓ-suc (ℓ-max o h)) (ℓ-max o h) (ℓ-max o h)
UNIVCATAt o h = FullSubbicategory (CATAt o h) isUnivalent

UNIVCAT : (ℓ : Level) → Bicategory (ℓ-suc ℓ) ℓ ℓ
UNIVCAT ℓ = UNIVCATAt ℓ ℓ

STRICTCAT : (ℓ : Level) → Bicategory (ℓ-suc ℓ) ℓ ℓ
STRICTCAT ℓ = FullSubbicategory (CAT ℓ) (λ C → isSet (C .ob))

isLocallyUnivalentUNIVCAT : ∀ {o h} (C D : UNIVCATAt o h .Ob)
                          → isUnivalent (UNIVCATAt o h .hom C D)
isLocallyUnivalentUNIVCAT C D = isUnivalentFUNCTOR (C .fst) (D .fst) (D .snd)
```

## Global univalence

Fix a univalent category $C$. By the structure identity principle for univalent categories, the total space of targets $D$ equipped with a weak equivalence from $C$ is contractible. Each adjoint equivalence yields a weak equivalence by forgetting its triangle identities. Conversely the identity adjoint structure transports over the contractible total space to equip every weak equivalence with an adjoint structure. Local univalence makes the adjoint structure on a given functor a proposition. The total space of adjoint equivalences is thus a retract of the contractible space, and the fundamental theorem of identity types applies.

```agda
open import Cubical.Foundations.Equiv using (_≃_; invEquiv; compEquiv)
open import Cubical.Foundations.Equiv.Fiberwise using (recognizeId)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (Σ-cong-equiv-snd; Σ≡PropEquiv; Σ≡Prop)
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁)
import Cubical.Categories.Equivalence.Base as CE
import Cubical.Categories.Equivalence.WeakEquivalence as W
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Properties using (isPropAdjointStructure)
import Bicategories.Univalence as BU

module _ {o h} where
  private U = UNIVCATAt o h

  adjointToWeak : {C D : U .Ob} {F : Functor (fst C) (fst D)}
                → AdjointStructure U {C} {D} F → W.isWeakEquivalence F
  adjointToWeak {C} {D} a = W.isEquiv→isWeakEquiv ∣ inverseData ∣₁
    where
    inverseData : CE.WeakInverse _
    inverseData .CE.WeakInverse.invFunc = a .AdjointStructure.inverse
    inverseData .CE.WeakInverse.η = FUNCTORIso→NatIso _ _ (a .AdjointStructure.unit)
    inverseData .CE.WeakInverse.ε = FUNCTORIso→NatIso _ _ (a .AdjointStructure.counit)

  module _ (C : U .Ob) where
    private
      TotalWeak = Σ (U .Ob) λ D → W.WeakEquivalence (fst C) (fst D)

      weakSingleton : TotalWeak ≃ singl C
      weakSingleton = Σ-cong-equiv-snd λ D →
        compEquiv (W.WeakEquivalence≃Path (snd C) (snd D)) (Σ≡PropEquiv λ _ → isPropIsUnivalent)

      totalContr : isContr TotalWeak
      totalContr = isOfHLevelRespectEquiv 0 (invEquiv weakSingleton) (isContrSingl C)

      center : TotalWeak
      center = C , W.weakEquivalence _ (adjointToWeak {C = C} {D = C}
                                         (snd (idAdjointEquivalence U C)))

      StructureAt : TotalWeak → Type _
      StructureAt (D , e) = AdjointStructure U {C} {D} (W.WeakEquivalence.func e)

      equip : (w : TotalWeak) → StructureAt w
      equip w = subst StructureAt (isContr→isProp totalContr center w)
                      (snd (idAdjointEquivalence U C))

      TotalAdjoint = Σ (U .Ob) (AdjointEquivalence U C)

      forget : TotalAdjoint → TotalWeak
      forget (D , F , a) = D , W.weakEquivalence F (adjointToWeak {C = C} {D = D} a)

      recover : TotalWeak → TotalAdjoint
      recover w = w .fst , W.WeakEquivalence.func (snd w) , equip w

      recoverForget : (v : TotalAdjoint) → recover (forget v) ≡ v
      recoverForget (D , F , a) i = D , F , unique (equip (forget (D , F , a))) a i
        where unique = isPropAdjointStructure U isLocallyUnivalentUNIVCAT {C} {D} F

```

For fixed $C$, the space of pairs consisting of a target $D$ and an adjoint equivalence $C\simeq D$ is now contractible. Its fiber over $D$ is therefore equivalent to $C=D$. This proves the global part and can be paired with the local result for functor categories.

```agda
    isGloballyUnivalentUNIVCAT : (D : U .Ob) → Cubical.Foundations.Equiv.isEquiv (pathToAdjointEquivalence U {C} {D})
    isGloballyUnivalentUNIVCAT D =
      recognizeId (AdjointEquivalence U C) (idAdjointEquivalence U C)
                  (isContrRetract forget recover recoverForget totalContr) D .snd

  opaque
    isUnivalentUNIVCAT : BU.isUnivalent (UNIVCATAt o h)
    isUnivalentUNIVCAT = isLocallyUnivalentUNIVCAT , isGloballyUnivalentUNIVCAT
```
