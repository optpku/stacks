module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.RegularSection
public import stacks_project.Chap66.«66_27_0_4_Comparison»
public import stacks_project.Chap66.Lemma_66_19_7_Point
public import stacks_project.Chap69.Lemma_69_16_2_ToSpec
public import stacks_project.Chap71.Definition_71_7_4_RegularSection

/-!
# Regular global functions on algebraic spaces

A global function of an algebraic space is a regular section of `𝒪_X` when multiplication
by it on the unit module is a monomorphism. Restriction to étale objects is the
`ΓSpec`-adjunct of the composite with `toSpecGamma`, using `ofOverPreimage` for the
underlying morphism of schemes over `S`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Restriction of `Γ(X, 𝒪_X)` to global functions on an étale scheme over `X`. -/
def restrictGlobalSectionRing (U : smallEtaleSite X) :
    globalSectionsRing X ⟶ Γ((smallEtaleToScheme X).obj U, ⊤) :=
  (Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
    ((ofOverPreimage (U.hom ≫ toSpecGamma X)).left ≫ specGamma_fst X).appTop

/-- `restrictGlobalSectionRing U` is the `ΓSpec` adjunct of the composite of `U` with
`toSpecGamma X`. -/
theorem restrictGlobalSectionRing_eq (U : smallEtaleSite X) :
    restrictGlobalSectionRing U =
      (Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
        ((ofOverPreimage (U.hom ≫ toSpecGamma X)).left ≫ specGamma_fst X).appTop :=
  sorry

/-- The restriction of a global function of `X` to an étale scheme over `X`. -/
abbrev restrictGlobalSection (U : smallEtaleSite X) (f : globalSectionsRing X) :
    Γ((smallEtaleToScheme X).obj U, ⊤) :=
  CommRingCat.Hom.hom (restrictGlobalSectionRing U) f

/-- `restrictGlobalSection` is the underlying ring map of `restrictGlobalSectionRing`. -/
theorem restrictGlobalSection_eq (U : smallEtaleSite X) (f : globalSectionsRing X) :
    restrictGlobalSection U f = CommRingCat.Hom.hom (restrictGlobalSectionRing U) f :=
  sorry

/-- Restriction of global functions as a morphism of underlying rings on the small étale
site. -/
def toStructureSheaf (U : smallEtaleSite X) :
    (forget₂ CommRingCat RingCat).obj (globalSectionsRing X) ⟶
      (structureSheaf X).obj.obj (op U) :=
  (forget₂ CommRingCat RingCat).map (restrictGlobalSectionRing U)

/-- `toStructureSheaf U` is `forget₂` of `restrictGlobalSectionRing U`. -/
theorem toStructureSheaf_eq (U : smallEtaleSite X) :
    toStructureSheaf U = (forget₂ CommRingCat RingCat).map (restrictGlobalSectionRing U) :=
  sorry

/-- Restriction of a global function is compatible with the unit `𝒪_X`-module. -/
theorem toUnitSection_naturality (f : globalSectionsRing X) :
    ∀ ⦃U V : (smallEtaleSite X)ᵒᵖ⦄ (i : U ⟶ V),
      (SheafOfModules.unit (structureSheaf X)).val.map i
          (RingCat.Hom.hom (toStructureSheaf U.unop) f) =
        RingCat.Hom.hom (toStructureSheaf V.unop) f :=
  sorry

/-- The global function `f` as a section of the unit `𝒪_X`-module, given objectwise by
restriction along `toStructureSheaf`. -/
def toUnitSection (f : globalSectionsRing X) :
    (SheafOfModules.unit (structureSheaf X) : X.Modules).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ RingCat.Hom.hom (toStructureSheaf U.unop) f)
    (toUnitSection_naturality f)

/-- On each étale object, `toUnitSection f` is the restriction of `f`. -/
theorem toUnitSection_eval (f : globalSectionsRing X) (U : (smallEtaleSite X)ᵒᵖ) :
    (toUnitSection f).val U = RingCat.Hom.hom (toStructureSheaf U.unop) f :=
  sorry

/-- The morphism `𝒪_X ⟶ 𝒪_X` given by multiplication by a global function. -/
abbrev structureSectionHom (f : globalSectionsRing X) :
    SheafOfModules.unit (structureSheaf X) ⟶ SheafOfModules.unit (structureSheaf X) :=
  regularSectionHom (SheafOfModules.unit (structureSheaf X) : X.Modules) (toUnitSection f)

/-- The induced multiplication map sends `1` to the restriction of `f`. -/
theorem structureSectionHom_app (f : globalSectionsRing X) (U : (smallEtaleSite X)ᵒᵖ) :
    (structureSectionHom f).val.app U (1 : (structureSheaf X).obj.obj U) =
      RingCat.Hom.hom (toStructureSheaf U.unop) f :=
  sorry

/-- A global function of an algebraic space is a regular section of `𝒪_X` when
multiplication by it on the unit `𝒪_X`-module is a monomorphism. -/
abbrev IsRegularStructureSection (f : globalSectionsRing X) : Prop :=
  IsRegularSection (SheafOfModules.unit (structureSheaf X) : X.Modules) (toUnitSection f)

/-- Regularity of a global function is monomorphicity of multiplication by that function. -/
theorem isRegularStructureSection_iff_mono (f : globalSectionsRing X) :
    IsRegularStructureSection f ↔ Mono (structureSectionHom f) :=
  sorry

/-- The stalk of `𝒪_X` at a geometric point, as a ring. -/
abbrev structureSheafStalk (xbar : GeometricPoint X) : RingCat.{u} :=
  ((xbar.toSmallEtalePoint.presheafFiber :
      ((smallEtaleSite X)ᵒᵖ ⥤ RingCat.{u}) ⥤ RingCat.{u}).obj
    (structureSheaf X).obj)

/-- `structureSheafStalk xbar` is the `RingCat`-valued étale-site fiber of `𝒪_X`. -/
theorem structureSheafStalk_eq (xbar : GeometricPoint X) :
    structureSheafStalk xbar =
      ((xbar.toSmallEtalePoint.presheafFiber :
          ((smallEtaleSite X)ᵒᵖ ⥤ RingCat.{u}) ⥤ RingCat.{u}).obj
        (structureSheaf X).obj) :=
  sorry

/-- The image of a global function in the étale local ring at `x̄` along a lift through an
étale neighbourhood. -/
def structureSectionGerm (xbar : GeometricPoint X) (U : smallEtaleSite X)
    (l : xbar.toSmallEtalePoint.fiber.obj U) (f : globalSectionsRing X) :
    structureSheafStalk xbar :=
  RingCat.Hom.hom
    (xbar.toSmallEtalePoint.toPresheafFiber U l (structureSheaf X).obj)
    (RingCat.Hom.hom (toStructureSheaf U) f)

/-- `structureSectionGerm` is the stalk coprojection of the restricted global function. -/
theorem structureSectionGerm_eq (xbar : GeometricPoint X) (U : smallEtaleSite X)
    (l : xbar.toSmallEtalePoint.fiber.obj U) (f : globalSectionsRing X) :
    structureSectionGerm xbar U l f =
      RingCat.Hom.hom
        (xbar.toSmallEtalePoint.toPresheafFiber U l (structureSheaf X).obj)
        (RingCat.Hom.hom (toStructureSheaf U) f) :=
  sorry

/-- A global function on a scheme is a regular section of its structure sheaf. -/
abbrev IsRegularSchemeStructureSection {Y : Scheme.{u}} (g : Γ(Y, ⊤)) : Prop :=
  RingedSpace.IsRegularSection (SheafOfModules.unit Y.toRingedSpace.ringCatSheaf)
    ((SheafOfModules.unit Y.toRingedSpace.ringCatSheaf).unitHomEquiv
      (RingedSpace.globalSectionMul g (SheafOfModules.unit Y.toRingedSpace.ringCatSheaf)))

/-- Scheme-theoretic regularity of a global function is regularity of the corresponding
section of the unit module. -/
theorem isRegularSchemeStructureSection_iff {Y : Scheme.{u}} (g : Γ(Y, ⊤)) :
    IsRegularSchemeStructureSection g ↔
      RingedSpace.IsRegularSection (SheafOfModules.unit Y.toRingedSpace.ringCatSheaf)
        ((SheafOfModules.unit Y.toRingedSpace.ringCatSheaf).unitHomEquiv
          (RingedSpace.globalSectionMul g
            (SheafOfModules.unit Y.toRingedSpace.ringCatSheaf))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
