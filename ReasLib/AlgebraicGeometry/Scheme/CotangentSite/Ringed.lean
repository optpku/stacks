/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.Sheafification
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.UniverseLift
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfSite

/-!
# Ringed topoi of polynomial affine diagrams

Pulling global functions back along a diagram induces a map between associated
sheaves. These sheaves are sheafifications of the displayed presheaves of
functions, including at the empty open; their comparison formulas use units.
The projection to the small Zariski site uses its existing lifted coefficient
sheaf. Unifying this construction with the algebraic-space version over an
arbitrary base site is a natural further generalization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CotangentSite

variable (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]

/-- Pullback along the diagram commutes with restriction of raw global functions. -/
theorem structurePresheafMap_naturality {P Q : (category Λ X)ᵒᵖ} (f : P ⟶ Q) :
    (structurePresheafComm Λ X).map f ≫ Q.unop.hom.left.appTop =
      P.unop.hom.left.appTop ≫ (inverseImageStructurePresheafComm Λ X).map f := sorry

/-- The raw global-functions map induced by the open-to-target morphism. -/
def structurePresheafMap :
    structurePresheafComm Λ X ⟶ inverseImageStructurePresheafComm Λ X where
  app P := P.unop.hom.left.appTop
  naturality := fun _ _ f ↦ structurePresheafMap_naturality Λ X f

/-- Pullback of global functions with coefficients lifted to the successor universe. -/
def structurePresheafMapLift :
    structurePresheafCommLift Λ X ⟶ inverseImageStructurePresheafCommLift Λ X :=
  Functor.whiskerRight (structurePresheafMap Λ X) CommRingCat.universeLift

/-- The map of associated commutative ring sheaves induced by diagram pullback. -/
def structureSheafMapComm :
    structureSheafComm Λ X ⟶ inverseImageStructureSheafComm Λ X :=
  (presheafToSheaf (topology Λ X) CommRingCat.{u + 1}).map
    (structurePresheafMapLift Λ X)

/-- The associated-sheaf pullback map commutes with the sheafification units. -/
theorem structureSheafMapComm_app (P : category Λ X) :
    (structureSheafUnit Λ X).app (op P) ≫
        (structureSheafMapComm Λ X).hom.app (op P) =
      (structurePresheafMapLift Λ X).app (op P) ≫
        (inverseImageStructureSheafUnit Λ X).app (op P) := sorry

/-- The ring-valued sheaf underlying associated affine-target functions. -/
def structureSheaf : Sheaf (topology Λ X) RingCat.{u + 1} :=
  CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (structureSheafComm Λ X)

/-- The ring-valued sheaf underlying associated open-vertex functions. -/
def inverseImageStructureSheaf : Sheaf (topology Λ X) RingCat.{u + 1} :=
  CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (inverseImageStructureSheafComm Λ X)

/-- Forgetting commutativity gives the ring-valued structure sheaf. -/
theorem structureSheafComm_forget :
    (sheafCompose (topology Λ X) (forget₂ CommRingCat RingCat.{u + 1})).obj
      (structureSheafComm Λ X) = structureSheaf Λ X := rfl

/-- Forgetting commutativity gives the ring-valued pulled-back structure sheaf. -/
theorem inverseImageStructureSheafComm_forget :
    (sheafCompose (topology Λ X) (forget₂ CommRingCat RingCat.{u + 1})).obj
      (inverseImageStructureSheafComm Λ X) = inverseImageStructureSheaf Λ X := rfl

/-- The ring-sheaf morphism induced by pulling functions back along diagrams. -/
def structureSheafMap : structureSheaf Λ X ⟶ inverseImageStructureSheaf Λ X :=
  CategoryTheory.Sheaf.ringSheafOfCommMap.{u + 1, u + 1, u} (structureSheafMapComm Λ X)

/-- Forgetting commutativity preserves the associated-sheaf pullback map. -/
theorem structureSheafMapComm_forget :
    (sheafCompose (topology Λ X) (forget₂ CommRingCat RingCat.{u + 1})).map
      (structureSheafMapComm Λ X) = structureSheafMap Λ X := rfl

/-- The ring-valued pullback square is mediated by the sheafification units. -/
theorem structureSheafMap_app (P : category Λ X) :
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map ((structureSheafUnit Λ X).app (op P)) ≫
        (structureSheafMap Λ X).hom.app (op P) =
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map ((structurePresheafMapLift Λ X).app (op P)) ≫
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
          ((inverseImageStructureSheafUnit Λ X).app (op P)) := sorry

/-- The polynomial affine diagram site with its associated target-function sheaf. -/
abbrev ringedSite : RingedSite.{u + 1, u, u + 1} :=
  ofRingSheaf (topology Λ X) (structureSheaf Λ X)

/-- The polynomial affine diagram site with its associated open-function sheaf. -/
abbrev inverseImageRingedSite : RingedSite.{u + 1, u, u + 1} :=
  ofRingSheaf (topology Λ X) (inverseImageStructureSheaf Λ X)

/-- The same-site morphism defined by the pullback of functions along diagrams. -/
def sameSite : RingedSite.Hom (inverseImageRingedSite Λ X) (ringedSite Λ X) :=
  SameSite.hom (structureSheafMap Λ X)

/-- The base functor of the same-site comparison is the identity. -/
theorem i_base : (sameSite Λ X).base = 𝟭 (category Λ X) := rfl

/-- The ring-sheaf comparison between associated open functions and continuous
pullback of the lifted small Zariski structure sheaf. -/
def inverseImageStructureSheafIso :
    inverseImageStructureSheaf Λ X ≅
      ((forgetZariski Λ X).sheafPushforwardContinuous RingCat.{u + 1}
        (topology Λ X) X.smallZariskiTopology).obj
          (Scheme.AssociatedModule.smallCommRingedSite .zariski X).structureSheaf :=
  (sheafCompose (topology Λ X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
    (inverseImageStructureSheafCommIso Λ X)

/-- The identity-on-topoi morphism induced by diagram pullback of functions. -/
def i : ToposHom (inverseImageRingedSite Λ X) (ringedSite Λ X) where
  toTopos := MorphismOfTopoiIn.id (topology Λ X)
  structureMap :=
    (MorphismOfTopoiIn.ringInverseImageIdIso.{u + 1, u, u + 1} (J₀ := topology Λ X) :
      (MorphismOfTopoiIn.id (topology Λ X) :
        MorphismOfTopoiIn.{u + 1, u + 1, u, u, u + 1} _ _).ringInverseImage ≅
          𝟭 (Sheaf (topology Λ X) RingCat.{u + 1})).hom.app (structureSheaf Λ X) ≫
      structureSheafMap Λ X

/-- Type-valued presheaves have pointwise right Kan extensions along the
opposite projection to the small Zariski site. -/
instance forgetZariski_op_hasPointwiseRightKanExtension
    (P : (category Λ X)ᵒᵖ ⥤ Type (u + 1)) :
    (forgetZariski Λ X).op.HasPointwiseRightKanExtension P := sorry

/-- The geometric morphism induced by the cocontinuous Zariski projection. -/
def toZariskiToTopos :
    MorphismOfTopoiIn X.smallZariskiTopology (topology Λ X) :=
  (forgetZariski Λ X).morphismOfTopoiInOfCocontinuous
    (topology Λ X) X.smallZariskiTopology

/-- The projection comparison is the ring-valued sheafification unit for open functions. -/
def toZariskiStructureMap :
    (forgetZariski Λ X).op ⋙
        (Scheme.AssociatedModule.smallCommRingedSite .zariski X).structureSheaf.obj ⟶
      (inverseImageRingedSite Λ X).structureSheaf.obj :=
  Functor.whiskerRight (inverseImageStructureSheafUnit Λ X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

/-- The inverse-image form of the projection structure map, obtained by adjunction. -/
def toZariskiStructureSheafMap :
    (toZariskiToTopos Λ X).ringInverseImage.obj
        (Scheme.AssociatedModule.smallCommRingedSite .zariski X).structureSheaf ⟶
      (inverseImageRingedSite Λ X).structureSheaf :=
  Cocontinuous.structureMap (X := inverseImageRingedSite Λ X)
    (Y := ofRingSheaf X.smallZariskiTopology
      (Scheme.AssociatedModule.smallCommRingedSite .zariski X).structureSheaf)
    (forgetZariski Λ X) (toZariskiStructureMap Λ X)

/-- The ringed-topos projection to the lifted small Zariski ringed site. -/
def toZariski : ToposHom (inverseImageRingedSite Λ X)
    (Scheme.AssociatedModule.smallCommRingedSite .zariski X) where
  toTopos := toZariskiToTopos Λ X
  structureMap := toZariskiStructureSheafMap Λ X

end AlgebraicGeometry.Scheme.CotangentSite
