module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RegularSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.ToSpec
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtalePoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.Scheme.Module.RegularSection
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Regular global functions on algebraic spaces

A global function is regular when its multiplication map on the unit structure-sheaf
module is a monomorphism. This condition can be tested on geometric stalks, on every
affine étale chart, or on a surjective étale scheme cover.
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
    ((Yoneda.fullyFaithful.preimage
          (U.hom ≫ toSpecGamma X : yoneda.obj U.left ⟶ yoneda.obj (specGammaOver X))).left ≫ specGamma_fst X).appTop

/-- `restrictGlobalSectionRing U` is the `ΓSpec` adjunct of the composite of `U` with
`toSpecGamma X`. -/
theorem restrictGlobalSectionRing_eq (U : smallEtaleSite X) :
    restrictGlobalSectionRing U =
      (Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
        ((Yoneda.fullyFaithful.preimage
          (U.hom ≫ toSpecGamma X : yoneda.obj U.left ⟶ yoneda.obj (specGammaOver X))).left ≫ specGamma_fst X).appTop :=
  rfl

/-- The restriction of a global function of `X` to an étale scheme over `X`. -/
abbrev restrictGlobalSection (U : smallEtaleSite X) (f : globalSectionsRing X) :
    Γ((smallEtaleToScheme X).obj U, ⊤) :=
  CommRingCat.Hom.hom (restrictGlobalSectionRing U) f

/-- `restrictGlobalSection` is the underlying ring map of `restrictGlobalSectionRing`. -/
theorem restrictGlobalSection_eq (U : smallEtaleSite X) (f : globalSectionsRing X) :
    restrictGlobalSection U f = CommRingCat.Hom.hom (restrictGlobalSectionRing U) f :=
  rfl

/-- Restriction of global functions as a morphism of underlying rings on the small étale
site. -/
def toStructureSheaf (U : smallEtaleSite X) :
    (forget₂ CommRingCat RingCat).obj (globalSectionsRing X) ⟶
      (structureSheaf X).obj.obj (op U) :=
  (forget₂ CommRingCat RingCat).map (restrictGlobalSectionRing U)

/-- `toStructureSheaf U` is `forget₂` of `restrictGlobalSectionRing U`. -/
theorem toStructureSheaf_eq (U : smallEtaleSite X) :
    toStructureSheaf U = (forget₂ CommRingCat RingCat).map (restrictGlobalSectionRing U) :=
  rfl

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
  rfl

/-- The morphism `𝒪_X ⟶ 𝒪_X` given by multiplication by a global function. -/
abbrev structureSectionHom (f : globalSectionsRing X) :
    SheafOfModules.unit (structureSheaf X) ⟶ SheafOfModules.unit (structureSheaf X) :=
  SheafOfModules.regularSectionHom (SheafOfModules.unit (structureSheaf X) : X.Modules) (toUnitSection f)

/-- The induced multiplication map sends `1` to the restriction of `f`. -/
theorem structureSectionHom_app (f : globalSectionsRing X) (U : (smallEtaleSite X)ᵒᵖ) :
    (structureSectionHom f).val.app U (1 : (structureSheaf X).obj.obj U) =
      RingCat.Hom.hom (toStructureSheaf U.unop) f :=
  sorry

/-- A global function of an algebraic space is a regular section of `𝒪_X` when
multiplication by it on the unit `𝒪_X`-module is a monomorphism. -/
abbrev IsRegularStructureSection (f : globalSectionsRing X) : Prop :=
  SheafOfModules.IsRegularSection (SheafOfModules.unit (structureSheaf X) : X.Modules) (toUnitSection f)

/-- Regularity of a global function is monomorphicity of multiplication by that function. -/
theorem isRegularStructureSection_iff_mono (f : globalSectionsRing X) :
    IsRegularStructureSection f ↔ Mono (structureSectionHom f) :=
  Iff.rfl

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
  rfl

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
  rfl

/-- A global function `f` of an algebraic space `X` is a regular section
of `𝒪_X` if and only if, for every geometric point `x̄` and every lift of `x̄` through an
étale neighbourhood, the image of `f` in the étale local ring `𝒪_{X, x̄}` is a
nonzerodivisor. -/
@[stacks 0844]
theorem isRegularStructureSection_iff_stalkwise (f : globalSectionsRing X) :
    IsRegularStructureSection f ↔
      ∀ (xbar : GeometricPoint X) (U : smallEtaleSite X)
        (l : xbar.toSmallEtalePoint.fiber.obj U),
        IsSMulRegular (structureSheafStalk xbar) (structureSectionGerm xbar U l f) :=
  sorry

/-- A global function `f` of an algebraic space `X` is a regular section
of `𝒪_X` if and only if, for every affine scheme étale over `X`, the restriction of `f` is
a nonzerodivisor of the coordinate ring. -/
@[stacks 0844]
theorem isRegularStructureSection_iff_forall_affineEtale (f : globalSectionsRing X) :
    IsRegularStructureSection f ↔
      ∀ U : affineEtaleSite X,
        IsSMulRegular Γ((smallEtaleToScheme X).obj U.obj, ⊤)
          (restrictGlobalSection U.obj f) :=
  sorry

/-- A global function `f` of an algebraic space `X` is a regular section
of `𝒪_X` if and only if there exists a scheme `U` and a surjective étale morphism `U ⟶ X`
such that the restriction of `f` is a regular section of `𝒪_U`. -/
@[stacks 0844]
theorem isRegularStructureSection_iff_exists_surjectiveEtale (f : globalSectionsRing X) :
    IsRegularStructureSection f ↔
      ∃ U : smallEtaleSite X,
        Surjective U.hom ∧
          Scheme.IsRegularStructureSection (restrictGlobalSection U f) :=
  sorry


end AlgebraicGeometry.AlgebraicSpace
