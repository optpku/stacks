/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift.LocalHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Functorial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationInclusion
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Parameters and compatible sections for first-order deformations

The internal Hom from pulled-back relative differentials to the conormal module
extends to the spaces-étale site and transports across a first-order thickening.
Compatible lifts form the automorphism-section sheaf of a cartesian diagram.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits CategoryTheory.ConcreteCategory TypeCat
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

variable {S : Scheme.{u}} {U U' I I' : AlgebraicSpace S}
variable (iU : U ⟶ U') (iI : I ⟶ I') (p' : I' ⟶ U') (p : I ⟶ U)
variable (Δ' : U' ⟶ I') (Δ : U ⟶ I)
variable [IsFirstOrderThickening iU] [IsFirstOrderThickening iI]
variable (hp : IsPullback p iI iU p') (hsec : Δ' ≫ p' = 𝟙 U')

/-- The infinitesimal parameter module `Hom_{O_U}(Δ^* Ω_{I/U}, C_{U/U'})`. -/
noncomputable def parameterModule : RingedSite.ModuleCat.{u + 1} (commRingedSiteLift U) :=
  Modules.internalHom
    ((Modules.pullback Δ).obj (Hom.relativeDifferentials p)) (conormalSheaf iU)

/-- `parameterModule` is the ringed-site internal Hom of `Δ^* Ω_{I/U}` with `C_{U/U'}`. -/
theorem parameterModule_eq :
    parameterModule iU p Δ =
      Modules.internalHom
        ((Modules.pullback Δ).obj (Hom.relativeDifferentials p)) (conormalSheaf iU) :=
  rfl

/-- A section of the Hom-parameter module is an actual morphism between the restrictions
of the original differential and conormal modules. Both directions use the componentwise
`ULift.up`/`ULift.down` construction. -/
noncomputable def parameterLocalHom (T : smallEtaleSite U) :
    (parameterModule iU p Δ).val.obj (op T) ≃
      (((Modules.pullback Δ).obj (Hom.relativeDifferentials p)).over T ⟶
        (conormalSheaf iU).over T) :=
  Modules.localHomEquiv
    ((Modules.pullback Δ).obj (Hom.relativeDifferentials p)) (conormalSheaf iU) T

/-- Evaluating a local parameter on a lower-universe section uses its supplied lifted
component map and then reads the result with `ULift.down`. -/
theorem parameterLocalHom_apply (T : smallEtaleSite U)
    (θ : (parameterModule iU p Δ).val.obj (op T)) (V : (Over T)ᵒᵖ)
    (s : (((Modules.pullback Δ).obj (Hom.relativeDifferentials p)).over T).val.obj V) :
    (((parameterLocalHom iU p Δ T) θ).val.app V).hom s =
      ((θ.val.app V).hom (ULift.up s)).down := rfl

/-- Lowering local parameters respects their addition. -/
theorem parameterLocalHom_add (T : smallEtaleSite U)
    (θ η : (parameterModule iU p Δ).val.obj (op T)) :
    parameterLocalHom iU p Δ T (θ + η) =
      parameterLocalHom iU p Δ T θ + parameterLocalHom iU p Δ T η := sorry

/-- The internal-Hom scalar acts by multiplication on the output section, after restricting
the scalar from the chart `T` to the tested slice object. -/
theorem parameterLocalHom_smul_apply (T : smallEtaleSite U)
    (r : (commRingedSiteLift U).structureSheaf.obj.obj (op T))
    (θ : (parameterModule iU p Δ).val.obj (op T)) (V : (Over T)ᵒᵖ)
    (s : (((Modules.pullback Δ).obj (Hom.relativeDifferentials p)).over T).val.obj V) :
    -- Local instance justification (defeq pin): use the stored action on (parameterModule iU p Δ).val.obj (op T).
    letI : Module ((commRingedSiteLift U).structureSheaf.obj.obj (op T))
        ((parameterModule iU p Δ).val.obj (op T)) :=
      ((parameterModule iU p Δ).val.obj (op T)).isModule
    -- Local instance justification (defeq pin): use the stored action on ((conormalSheaf iU).over T).val.obj V.
    letI : Module (((structureSheaf U).over T).obj.obj V)
        (((conormalSheaf iU).over T).val.obj V) :=
      (((conormalSheaf iU).over T).val.obj V).isModule
    let lowerScalar : (((structureSheaf U).over T).obj.obj V) :=
      (structureSheaf U).obj.map V.unop.hom.op r.down
    (((parameterLocalHom iU p Δ T) (r • θ)).val.app V).hom s =
      lowerScalar •
        (((parameterLocalHom iU p Δ T) θ).val.app V).hom s := sorry

/-- The forgotten Type sheaf of `parameterModule` on the small étale site of `U`. -/
noncomputable def parameterTypeSheaf : Sheaf (smallEtaleTopology U) (Type (u + 1)) :=
  ⟨(parameterModule iU p Δ).val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}, sorry⟩

/-- `parameterTypeSheaf` is the Type-valued sheaf underlying `parameterModule`. -/
theorem parameterTypeSheaf_obj :
    (parameterTypeSheaf iU p Δ).obj =
      (parameterModule iU p Δ).val.presheaf ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1} :=
  rfl

/-- Extension of `parameterTypeSheaf` along `smallEtaleToSpaces U` to `U_spaces,étale`. -/
noncomputable def parameterSheafSpaces : Sheaf (spacesEtaleTopology U) (Type (u + 1)) :=
  ((smallEtaleToSpaces U).sheafPushforwardCocontinuous (Type (u + 1))
      (smallEtaleTopology U) (spacesEtaleTopology U)).obj
    (parameterTypeSheaf iU p Δ)

/-- `parameterSheafSpaces` is cocontinuous extension of `parameterTypeSheaf`. -/
theorem parameterSheafSpaces_eq :
    parameterSheafSpaces iU p Δ =
      ((smallEtaleToSpaces U).sheafPushforwardCocontinuous (Type (u + 1))
          (smallEtaleTopology U) (spacesEtaleTopology U)).obj
        (parameterTypeSheaf iU p Δ) :=
  rfl

/-- Transport of the parameter sheaf across the equivalence of spaces-étale sites
induced by a first-order thickening. -/
noncomputable def parameterSheafEtale : Sheaf (spacesEtaleTopology U') (Type (u + 1)) :=
  ((spacesEtalePullback iU).sheafPushforwardContinuous (Type (u + 1))
      (spacesEtaleTopology U') (spacesEtaleTopology U)).obj
    (parameterSheafSpaces iU p Δ)

/-- `parameterSheafEtale` is continuous pushforward of `parameterSheafSpaces` along
`spacesEtalePullback iU`. -/
theorem parameterSheafEtale_eq :
    parameterSheafEtale iU p Δ =
      ((spacesEtalePullback iU).sheafPushforwardContinuous (Type (u + 1))
          (spacesEtaleTopology U') (spacesEtaleTopology U)).obj
        (parameterSheafSpaces iU p Δ) :=
  rfl

/-- The global zero section of the internal-Hom parameter module. -/
def parameterModuleZeroSection :
    (parameterModule iU p Δ).val.sections :=
  PresheafOfModules.sectionsMk
    (fun T ↦ (0 : (parameterModule iU p Δ).val.obj T)) sorry

/-- Objectwise, `parameterModuleZeroSection` is the zero element of `parameterModule`. -/
theorem parameterModuleZeroSection_eval (T : (smallEtaleSite U)ᵒᵖ) :
    (parameterModuleZeroSection iU p Δ).eval T = 0 :=
  rfl

/-- The cone of zero values presenting the image of `parameterModuleZeroSection`
in the right Kan fibre used by `parameterSheafEtale`. -/
noncomputable def parameterSheafEtaleZeroCone :
    Cone
      (StructuredArrow.proj
          (op ((spacesEtalePullback iU).obj (spacesEtaleSite.self U')))
          (smallEtaleToSpaces U).op ⋙
        (parameterTypeSheaf iU p Δ).obj) where
  pt := PUnit.{u + 2}
  π :=
    { app := fun a ↦
        TypeCat.ofHom fun _ ↦ (parameterModuleZeroSection iU p Δ).eval a.right
      naturality := sorry }

/-- The cone point of `parameterSheafEtaleZeroCone` is `PUnit`. -/
theorem parameterSheafEtaleZeroCone_pt :
    (parameterSheafEtaleZeroCone iU p Δ).pt = PUnit.{u + 2} :=
  rfl

/-- The zero section of `parameterSheafEtale` at `spacesEtaleSite.self U'`, obtained
by forgetting the zero of `parameterModule` from `AddCommGrpCat` to `Type` and
transporting along `smallEtaleToSpaces` and `spacesEtalePullback iU`. -/
noncomputable def parameterSheafEtaleZero :
    (parameterSheafEtale iU p Δ).obj.obj (op (spacesEtaleSite.self U')) :=
  ((smallEtaleToSpaces U).op.ranObjObjIsoLimit (parameterTypeSheaf iU p Δ).obj
      (op ((spacesEtalePullback iU).obj (spacesEtaleSite.self U')))).inv
    (limit.lift _ (parameterSheafEtaleZeroCone iU p Δ) PUnit.unit)

/-- `parameterSheafEtaleZero` is the right-Kan transport of `parameterModuleZeroSection`. -/
theorem parameterSheafEtaleZero_eq :
    parameterSheafEtaleZero iU p Δ =
      ((smallEtaleToSpaces U).op.ranObjObjIsoLimit (parameterTypeSheaf iU p Δ).obj
          (op ((spacesEtalePullback iU).obj (spacesEtaleSite.self U')))).inv
        (limit.lift _ (parameterSheafEtaleZeroCone iU p Δ) PUnit.unit) :=
  rfl

/-- The set of automorphisms of a gerbe-of-lifts object, identified with the
deformation sheaf of `(U ⊂ U')` and `(I ⊂ I')` over `(U ⊂ U')` along `𝟙 U'` and `p'`. -/
def autSections (hΔ : IsPullback Δ iU iI Δ') (V' : spacesEtaleSite U') :
    Set (V'.left ⟶ I') :=
  sections (𝟙 U') p' iU iI Δ (Hom.Conormal.map hΔ.toCommSq) V'

/-- Automorphism sections are compatible lifts with the diagonal conormal comparison. -/
theorem autSections_eq (hΔ : IsPullback Δ iU iI Δ') (V' : spacesEtaleSite U') :
    autSections iU iI p' Δ' Δ hΔ V' =
      sections (𝟙 U') p' iU iI Δ (Hom.Conormal.map hΔ.toCommSq) V' :=
  rfl

include hp hsec in
/-- In a cartesian first-order diagram, automorphism sections are exactly the maps
with the prescribed ambient projection and reduced diagonal. -/
theorem mem_autSections_iff (hΔ : IsPullback Δ iU iI Δ')
    (V' : spacesEtaleSite U') (a' : V'.left ⟶ I') :
    a' ∈ autSections iU iI p' Δ' Δ hΔ V' ↔
      a' ≫ p' = V'.hom ∧
        closedι iU V' ≫ a' = toSource iU V' ≫ Δ ≫ iI := sorry

/-- Restriction of section morphisms preserves identities and composition. -/
private theorem autPresheaf_laws :
    (∀ (V' : spacesEtaleSite U') (a' : V'.left ⟶ I'),
      restrictHom (𝟙 V') a' = a') ∧
    (∀ {V' W' Z' : spacesEtaleSite U'} (f : V' ⟶ W') (g : W' ⟶ Z')
      (a' : Z'.left ⟶ I'),
      restrictHom f (restrictHom g a') = restrictHom (f ≫ g) a') := sorry

/-- The Type-valued presheaf of automorphism sections on `U'_spaces,étale`. -/
noncomputable def autPresheaf (hΔ : IsPullback Δ iU iI Δ') :
    (spacesEtaleSite U')ᵒᵖ ⥤ Type (u + 1) where
  obj V' := { a' : V'.unop.left ⟶ I' // a' ∈ autSections iU iI p' Δ' Δ hΔ V'.unop }
  map f :=
    ConcreteCategory.ofHom <| TypeCat.Fun.mk <|
      Subtype.map (restrictHom f.unop) fun a' ha' ↦
        mem_sections_restrictHom (𝟙 U') p' iU iI Δ
          (Hom.Conormal.map hΔ.toCommSq) f.unop a' ha'
  map_id V' := by
    ext a'
    exact (autPresheaf_laws (U' := U') (I' := I')).1 V'.unop a'.val
  map_comp f g := by
    ext a'
    exact ((autPresheaf_laws (U' := U') (I' := I')).2 g.unop f.unop a'.val).symm

/-- Objectwise, `autPresheaf` is the type of compatible lifts in `autSections`. -/
theorem autPresheaf_obj (hΔ : IsPullback Δ iU iI Δ') (V' : (spacesEtaleSite U')ᵒᵖ) :
    (autPresheaf iU iI p' Δ' Δ hΔ).obj V' =
      { a' : V'.unop.left ⟶ I' // a' ∈ autSections iU iI p' Δ' Δ hΔ V'.unop } :=
  rfl

/-- The sheaf of sets `Aut(ξ)` on `U'_spaces,étale`. -/
noncomputable def autSheaf (hΔ : IsPullback Δ iU iI Δ') :
    Sheaf (spacesEtaleTopology U') (Type (u + 1)) :=
  ⟨autPresheaf iU iI p' Δ' Δ hΔ, sorry⟩

/-- The underlying presheaf of `autSheaf` is `autPresheaf`. -/
theorem autSheaf_obj (hΔ : IsPullback Δ iU iI Δ') :
    (autSheaf iU iI p' Δ' Δ hΔ).obj = autPresheaf iU iI p' Δ' Δ hΔ :=
  rfl

/-- The diagonal `Δ'` is a section of `autSections` on the identity object of
`U'_spaces,étale`. -/
theorem diagonal_mem_autSections (hΔ : IsPullback Δ iU iI Δ') (hsec : Δ' ≫ p' = 𝟙 U') :
    Δ' ∈ autSections iU iI p' Δ' Δ hΔ (spacesEtaleSite.self U') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
