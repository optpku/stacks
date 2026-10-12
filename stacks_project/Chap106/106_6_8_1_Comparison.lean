/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Definition_76_6_5_Conormal

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap66.Lemma_66_18_3
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap76.«76_17_4_1_Deformation»

/-!
# Hom parameters and Aut sections for first-order lifts of algebraic spaces

In the first-order gerbe-of-lifts setting, the infinitesimal parameter sheaf is
`Hom_{O_U}(Δ^* Ω_{I/U}, C_{U/U'})`, constructed as the ringed-site internal Hom of
the pulled-back relative differentials and the conormal sheaf of `U ⊂ U'`. After the
identification of tag 061B, `Aut(ξ)` is the set-valued deformation sheaf of the
thickenings `(U ⊂ U')` and `(I ⊂ I')` over `(U ⊂ U')` along `𝟙 U'` and `p'`.

The sheaf `Ω_{I/U}` is the sheafification of Kähler differentials of
`inverseImageStructureSheafHom p`, so that it lives on the same import path as
`conormalSheaf` and `Hom.Deformation.sections`.
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

/-- The sheaf of relative differentials `Ω_{I/U}` of `p : I ⟶ U`, as the
sheafification of Kähler differentials of `inverseImageStructureSheafHom p`. -/
noncomputable def relativeDifferentialsOver : I.Modules :=
  (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf I).obj)).obj
    (relativeDifferentials' (inverseImageStructureSheafHom p).hom)

/-- `relativeDifferentialsOver p` is the sheafification of the Kähler differentials
of `inverseImageStructureSheafHom p`. -/
theorem relativeDifferentialsOver_eq :
    relativeDifferentialsOver p =
      (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf I).obj)).obj
        (relativeDifferentials' (inverseImageStructureSheafHom p).hom) :=
  rfl

/-- The infinitesimal parameter module `Hom_{O_U}(Δ^* Ω_{I/U}, C_{U/U'})`. -/
noncomputable def parameterModule : RingedSite.ModuleCat.{u + 1} (commRingedSiteLift U) :=
  Modules.internalHom
    ((Modules.pullback Δ).obj (relativeDifferentialsOver p)) (conormalSheaf iU)

/-- `parameterModule` is the ringed-site internal Hom of `Δ^* Ω_{I/U}` with `C_{U/U'}`. -/
theorem parameterModule_eq :
    parameterModule iU p Δ =
      Modules.internalHom
        ((Modules.pullback Δ).obj (relativeDifferentialsOver p)) (conormalSheaf iU) :=
  rfl

/-- The zero morphism `Δ^* Ω_{I/U} ⟶ C_{U/U'}`. -/
def parameterZero :
    (Modules.pullback Δ).obj (relativeDifferentialsOver p) ⟶ conormalSheaf iU :=
  0

/-- The zero parameter is the zero morphism of `O_U`-modules. -/
theorem parameterZero_eq : parameterZero iU p Δ = 0 :=
  rfl

/-- The forgotten Type sheaf of `parameterModule` on the small étale site of `U`. -/
noncomputable def parameterTypeSheaf : Sheaf (smallEtaleTopology U) (Type (u + 1)) :=
  ⟨(parameterModule iU p Δ).val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}, sorry⟩

/-- `parameterTypeSheaf` is the Type-valued sheaf underlying `parameterModule`. -/
theorem parameterTypeSheaf_obj :
    (parameterTypeSheaf iU p Δ).obj =
      (parameterModule iU p Δ).val.presheaf ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1} :=
  rfl

/-- Extension of `parameterTypeSheaf` along `smallEtaleInclusion U` to `U_spaces,étale`. -/
noncomputable def parameterSheafSpaces : Sheaf (spacesEtaleTopology U) (Type (u + 1)) :=
  ((smallEtaleInclusion U).sheafPushforwardCocontinuous (Type (u + 1))
      (smallEtaleTopology U) (spacesEtaleTopology U)).obj
    (parameterTypeSheaf iU p Δ)

/-- `parameterSheafSpaces` is cocontinuous extension of `parameterTypeSheaf`. -/
theorem parameterSheafSpaces_eq :
    parameterSheafSpaces iU p Δ =
      ((smallEtaleInclusion U).sheafPushforwardCocontinuous (Type (u + 1))
          (smallEtaleTopology U) (spacesEtaleTopology U)).obj
        (parameterTypeSheaf iU p Δ) :=
  rfl

/-- Transport of `parameterSheafSpaces` along `spacesEtalePullback iU`, using the
identification `U_spaces,étale = U'_spaces,étale` of tag 05ZL. -/
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

/-- The global zero section of `parameterModule`, equivalently the forgotten
`AddCommGrpCat`-valued image of `parameterZero`. -/
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
          (smallEtaleInclusion U).op ⋙
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
transporting along `smallEtaleInclusion` and `spacesEtalePullback iU`. -/
noncomputable def parameterSheafEtaleZero :
    (parameterSheafEtale iU p Δ).obj.obj (op (spacesEtaleSite.self U')) :=
  ((smallEtaleInclusion U).op.ranObjObjIsoLimit (parameterTypeSheaf iU p Δ).obj
      (op ((spacesEtalePullback iU).obj (spacesEtaleSite.self U')))).inv
    (limit.lift _ (parameterSheafEtaleZeroCone iU p Δ) PUnit.unit)

/-- `parameterSheafEtaleZero` is the right-Kan transport of `parameterModuleZeroSection`. -/
theorem parameterSheafEtaleZero_eq :
    parameterSheafEtaleZero iU p Δ =
      ((smallEtaleInclusion U).op.ranObjObjIsoLimit (parameterTypeSheaf iU p Δ).obj
          (op ((spacesEtalePullback iU).obj (spacesEtaleSite.self U')))).inv
        (limit.lift _ (parameterSheafEtaleZeroCone iU p Δ) PUnit.unit) :=
  rfl

/-- The canonical conormal comparison of the cartesian restriction square of `Δ'`. -/
noncomputable def conormalComparison (hΔ : IsPullback Δ iU iI Δ') :
    (Modules.pullback Δ).obj (conormalSheaf iI) ⟶ conormalSheaf iU :=
  Conormal.map hΔ.toCommSq

/-- `conormalComparison` is `Conormal.map` of the diagonal square. -/
theorem conormalComparison_eq (hΔ : IsPullback Δ iU iI Δ') :
    conormalComparison iU iI Δ' Δ hΔ = Conormal.map hΔ.toCommSq :=
  rfl

/-- The set of automorphisms of a gerbe-of-lifts object, identified with the
deformation sheaf of `(U ⊂ U')` and `(I ⊂ I')` over `(U ⊂ U')` along `𝟙 U'` and `p'`. -/
def autSections (hΔ : IsPullback Δ iU iI Δ') (V' : spacesEtaleSite U') :
    Set (V'.left ⟶ I') :=
  sections (𝟙 U') p' iU iI Δ (conormalComparison iU iI Δ' Δ hΔ) V'

/-- `autSections` is the 061B deformation sheaf of `Δ` with the diagonal conormal comparison. -/
theorem autSections_eq (hΔ : IsPullback Δ iU iI Δ') (V' : spacesEtaleSite U') :
    autSections iU iI p' Δ' Δ hΔ V' =
      sections (𝟙 U') p' iU iI Δ (conormalComparison iU iI Δ' Δ hΔ) V' :=
  rfl

/-- Membership in `autSections` is compatibility over `p'`, restriction to `Δ`, and
matching of the prescribed conormal comparison. -/
theorem mem_autSections_iff (hΔ : IsPullback Δ iU iI Δ')
    (V' : spacesEtaleSite U') (a' : V'.left ⟶ I') :
    a' ∈ autSections iU iI p' Δ' Δ hΔ V' ↔
      IsCompatible (𝟙 U') p' iU iI Δ (conormalComparison iU iI Δ' Δ hΔ) V' a' :=
  sorry

/-- The Type-valued presheaf of automorphism sections on `U'_spaces,étale`. -/
noncomputable def autPresheaf (hΔ : IsPullback Δ iU iI Δ') :
    (spacesEtaleSite U')ᵒᵖ ⥤ Type (u + 1) where
  obj V' := { a' : V'.unop.left ⟶ I' // a' ∈ autSections iU iI p' Δ' Δ hΔ V'.unop }
  map f :=
    ConcreteCategory.ofHom <| TypeCat.Fun.mk <|
      Subtype.map (restrictHom f.unop) fun a' ha' ↦
        mem_sections_restrictHom (𝟙 U') p' iU iI Δ
          (conormalComparison iU iI Δ' Δ hΔ) f.unop a' ha'
  map_id := sorry
  map_comp := sorry

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

/-- The chosen global diagonal section `Δ' : U' ⟶ I'`. -/
def diagonalHom : U' ⟶ I' :=
  Δ'

/-- `diagonalHom` is the given diagonal morphism `Δ'`. -/
theorem diagonalHom_eq : diagonalHom Δ' = Δ' :=
  rfl

/-- The diagonal `Δ'` is a section of `autSections` on the identity object of
`U'_spaces,étale`. -/
theorem diagonalHom_mem (hΔ : IsPullback Δ iU iI Δ') (hsec : Δ' ≫ p' = 𝟙 U') :
    diagonalHom Δ' ∈ autSections iU iI p' Δ' Δ hΔ (spacesEtaleSite.self U') :=
  sorry

/-- The sheaf isomorphism of tag 0CKH is pointed, sending the named zero section
of `parameterSheafEtale` at `spacesEtaleSite.self U'` to `Δ'`. -/
theorem parameter_iso_aut_zero (hΔ : IsPullback Δ iU iI Δ')
    (hp : IsPullback p iI iU p') (hsec : Δ' ≫ p' = 𝟙 U') :
    ∃ e : parameterSheafEtale iU p Δ ≅ autSheaf iU iI p' Δ' Δ hΔ,
      e.hom.hom.app (op (spacesEtaleSite.self U'))
          (parameterSheafEtaleZero iU p Δ) =
        Subtype.mk (diagonalHom Δ')
          (diagonalHom_mem iU iI p' Δ' Δ hΔ hsec) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
