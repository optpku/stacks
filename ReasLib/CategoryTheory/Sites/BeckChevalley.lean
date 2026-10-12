/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.SheafificationComparison
public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.CategoryTheory.Sites.Over.Square
import Mathlib.Tactic.CrossRefAttribute

/-!
# Beck-Chevalley comparisons for sites

This leaf packages the sheaf-theoretic Beck-Chevalley comparison associated
to a 2-commutative square of functors of sites.  It is independent of any
particular textbook presentation or geometry of the sites.

The ordinary slice-category square is owned by `Over`, the corresponding
square of localized sheaf pullbacks by `GrothendieckTopology`, and the
general direct-image/inverse-image comparison by `CatCommSq`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

namespace Over

variable {C : Type u₁} [Category.{v₁} C]
variable {U' U V' V : C}

section PostMap

variable {D : Type u₂} [Category.{v₂} D]
variable (u : D ⥤ C) {V V' : D} (b : V' ⟶ V)

/-- The identity on the image carrier satisfies the triangle required for the canonical
isomorphism between the two slice objects. -/
theorem postMapIsoApp_hom (P : Over V') :
    (Iso.refl _).hom ≫ ((Over.map b ⋙ Over.post u).obj P).hom =
      ((Over.post u ⋙ Over.map (u.map b)).obj P).hom := sorry

/-- The component of the canonical square comparing postcomposition by `u` with changing the
slice base along `b`. -/
noncomputable def postMapIsoApp (P : Over V') :
    ((Over.post u ⋙ Over.map (u.map b)).obj P) ≅
      ((Over.map b ⋙ Over.post u).obj P) :=
  Over.isoMk (Iso.refl _) (postMapIsoApp_hom u b P)

/-- Naturality of the canonical comparison between postcomposition and changing the slice
base. -/
theorem postMapIsoApp_naturality {P Q : Over V'} (g : P ⟶ Q) :
    (Over.post u ⋙ Over.map (u.map b)).map g ≫ (postMapIsoApp u b Q).hom =
      (postMapIsoApp u b P).hom ≫ (Over.map b ⋙ Over.post u).map g := sorry

/-- Postcomposition by a functor commutes canonically with changing the base of a slice along
an arrow. -/
noncomputable def postMapIso :
    Over.post u ⋙ Over.map (u.map b) ≅ Over.map b ⋙ Over.post u :=
  NatIso.ofComponents (postMapIsoApp u b)
    (fun g ↦ postMapIsoApp_naturality u b g)

/-- The canonical `2`-commutative square formed by postcomposition and changing slice bases. -/
@[implicit_reducible]
noncomputable def postMapCommSq :
    CatCommSq (Over.post u) (Over.map b) (Over.map (u.map b)) (Over.post u) where
  iso := postMapIso u b

end PostMap

end Over

namespace CatCommSq

namespace BeckChevalley

variable {C' : Type u₁} [Category.{v₁} C']
variable {C : Type u₂} [Category.{v₂} C]
variable {D' : Type u₃} [Category.{v₃} D']
variable {D : Type u₄} [Category.{v₄} D]

variable (J' : GrothendieckTopology C') (J : GrothendieckTopology C)
variable (K' : GrothendieckTopology D') (K : GrothendieckTopology D)

variable {u' : C' ⥤ D'} {v' : C' ⥤ C} {u : C ⥤ D} {v : D' ⥤ D}

variable [Functor.IsCocontinuous u J K] [Functor.IsCocontinuous u' J' K']
variable [Functor.IsContinuous v K' K] [Functor.IsContinuous v' J' J]
variable [∀ F : C'ᵒᵖ ⥤ Type w, u'.op.HasPointwiseRightKanExtension F]
variable [∀ F : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension F]
variable [HasWeakSheafify J' (Type w)] [HasWeakSheafify J (Type w)]

/-- The comparison on inverse-image functors induced by a 2-commutative
square of continuous and cocontinuous functors of sites. -/
noncomputable def inverseImageComparison
    (sq : CatCommSq v' u' u v) :
    v.sheafPushforwardContinuous (Type w) K' K ⋙
        u'.sheafPullbackCocontinuous (Type w) J' K' ⟶
      u.sheafPullbackCocontinuous (Type w) J K ⋙
        v'.sheafPushforwardContinuous (Type w) J' J :=
  let leftIso :
      v.sheafPushforwardContinuous (Type w) K' K ⋙
          u'.sheafPullbackCocontinuous (Type w) J' K' ≅
        sheafToPresheaf K (Type w) ⋙
          (Functor.whiskeringLeft D'ᵒᵖ Dᵒᵖ (Type w)).obj v.op ⋙
          (Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op ⋙
          presheafToSheaf J' (Type w) :=
    Iso.refl _ ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (v.sheafPushforwardContinuousCompSheafToPresheafIso (Type w) K' K)
          ((Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op ⋙
            presheafToSheaf J' (Type w)) ≪≫
          Functor.associator _ _ _
  let middleIso :
      sheafToPresheaf K (Type w) ⋙
          (Functor.whiskeringLeft D'ᵒᵖ Dᵒᵖ (Type w)).obj v.op ⋙
          (Functor.whiskeringLeft C'ᵒᵖ D'ᵒᵖ (Type w)).obj u'.op ⋙
          presheafToSheaf J' (Type w) ≅
        sheafToPresheaf K (Type w) ⋙
          (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op ⋙
          (Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ (Type w)).obj v'.op ⋙
          presheafToSheaf J' (Type w) :=
    let oppositeSourceComp : u'.op ⋙ v.op ≅ (u' ⋙ v).op := Iso.refl _
    let oppositeTargetComp : (v' ⋙ u).op ≅ v'.op ⋙ u.op := Iso.refl _
    Functor.isoWhiskerLeft
      (sheafToPresheaf K (Type w))
      (Functor.isoWhiskerRight
        ((u'.op.whiskeringLeftObjCompIso v.op).symm ≪≫
          (Functor.whiskeringLeft C'ᵒᵖ Dᵒᵖ (Type w)).mapIso
            (oppositeSourceComp ≪≫
              (NatIso.op sq.iso.symm).symm ≪≫
              oppositeTargetComp) ≪≫
          v'.op.whiskeringLeftObjCompIso u.op)
        (presheafToSheaf J' (Type w)))
  let rightComparison :
      sheafToPresheaf K (Type w) ⋙
          (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op ⋙
          (Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ (Type w)).obj v'.op ⋙
          presheafToSheaf J' (Type w) ⟶
        u.sheafPullbackCocontinuous (Type w) J K ⋙
          v'.sheafPushforwardContinuous (Type w) J' J :=
    Functor.whiskerLeft
      (sheafToPresheaf K (Type w) ⋙
        (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op)
      (v'.continuousSheafificationComparison J' J)
  leftIso.hom ≫ middleIso.hom ≫ rightComparison

/-- The direct-image/inverse-image Beck--Chevalley morphism obtained as the mate of
`inverseImageComparison`. -/
@[stacks 0FN1 "comparison"]
noncomputable def comparison
    (sq : CatCommSq v' u' u v) :
    u.sheafPushforwardCocontinuous (Type w) J K ⋙
        v.sheafPushforwardContinuous (Type w) K' K ⟶
      v'.sheafPushforwardContinuous (Type w) J' J ⋙
        u'.sheafPushforwardCocontinuous (Type w) J' K' :=
  mateEquiv
    (u.sheafPullbackCocontinuousAdjunction J K)
    (u'.sheafPullbackCocontinuousAdjunction J' K')
    (inverseImageComparison J' J K' K sq)

/-- Guitart exactness of a square makes its direct-image/inverse-image
Beck-Chevalley morphism invertible. -/
theorem comparison_isIso_of_guitartExact
    [Functor.IsCocontinuous v K' K]
    [Functor.IsCocontinuous v' J' J]
    (sq : CatCommSq v' u' u v)
    (hsq : TwoSquare.GuitartExact sq.iso.hom) :
    IsIso (comparison J' J K' K sq) := sorry

/-- Finality of the structured-arrow comparison functors makes the direct-image/inverse-image
Beck-Chevalley morphism invertible. -/
@[stacks 0FN1 "finality criterion"]
theorem comparison_isIso_of_final
    [Functor.IsCocontinuous v K' K]
    [Functor.IsCocontinuous v' J' J]
    (sq : CatCommSq v' u' u v)
    (hfinal : ∀ V' : D', (TwoSquare.costructuredArrowRightwards sq.iso.hom V').Final) :
    IsIso (comparison J' J K' K sq) := sorry

end BeckChevalley

end CatCommSq

end CategoryTheory
