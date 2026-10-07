module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.SquareZeroExtension

/-!
# Splittings of first-order thickenings of ringed spaces

A retraction of a first-order thickening identifies the direct image of the
structure sheaf with the square-zero extension by its ideal module.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- Direct image of the structure sheaf of `X'` along a morphism `π : X' ⟶ X`. -/
abbrev pushforwardSheaf {X X' : RingedSpace.{u}} (π : X' ⟶ X) :
    TopCat.Sheaf CommRingCat.{u} X :=
  (TopCat.Sheaf.pushforward CommRingCat.{u} π.hom.base).obj X'.sheaf

/-- The open `π⁻¹ U`, viewed as an object of the opposite category of opens of `X'`. -/
abbrev preimageOp {X X' : RingedSpace.{u}} (π : X' ⟶ X) (U : (Opens X)ᵒᵖ) : (Opens X')ᵒᵖ :=
  op ((Opens.map π.hom.base).obj (unop U))

/-- The objectwise identification of `π_* 𝒪_{X'}` with sections of `𝒪_{X'}` on `π⁻¹ U`. -/
def pushforwardSheafApp {X X' : RingedSpace.{u}} (π : X' ⟶ X) (U : (Opens X)ᵒᵖ) :
    X'.sheaf.obj.obj (preimageOp π U) ⟶ (pushforwardSheaf π).obj.obj U :=
  𝟙 _


/-- Pushforward of `𝒪_X` along `i ≫ π` compared with pushforward along the identity. -/
def retractionPushforwardEq {X X' : RingedSpace.{u}} {i : X ⟶ X'} {π : X' ⟶ X}
    (hπ : i ≫ π = 𝟙 X) :
    (i ≫ π).hom.base _* X.presheaf ≅ (𝟙 X : X ⟶ X).hom.base _* X.presheaf :=
  TopCat.Presheaf.pushforwardEq (congrArg (fun f : X ⟶ X ↦ f.hom.base) hπ) X.presheaf

/-- The identification `π_* i_* 𝒪_X ≅ 𝒪_X` induced by `i ≫ π = 𝟙 X`. -/
def retractionPushforwardHom {X X' : RingedSpace.{u}} {i : X ⟶ X'} {π : X' ⟶ X}
    (hπ : i ≫ π = 𝟙 X) :
    (TopCat.Sheaf.pushforward CommRingCat.{u} π.hom.base).obj
        ((TopCat.Sheaf.pushforward CommRingCat.{u} i.hom.base).obj X.sheaf) ⟶
      X.sheaf :=
  ObjectProperty.homMk (retractionPushforwardEq hπ).hom

/-- The transported structure-sheaf map `π_* 𝒪_{X'} ⟶ 𝒪_X` obtained from `i^♯`. -/
def transportedISharp {X X' : RingedSpace.{u}} (i : X ⟶ X') (π : X' ⟶ X)
    (hπ : i ≫ π = 𝟙 X) :
    pushforwardSheaf π ⟶ X.sheaf :=
  (TopCat.Sheaf.pushforward CommRingCat.{u} π.hom.base).map (commRingSheafPushforwardMap i) ≫
    retractionPushforwardHom hπ


/-- Comparison `π_* Ker(i^♯) ⟶ ℐ` assembled from the pullback-pushforward unit, composition,
and the retraction `i ≫ π = 𝟙 X`. -/
def kernelPushforwardHom {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
    (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) :
    (π _*).obj (kernelIdealSheaf i) ⟶ idealModule i :=
  (π _*).map ((pullbackPushforwardAdjunction i).unit.app (kernelIdealSheaf i)) ≫
    (pushforwardCompIso i π).inv.app (idealModule i) ≫
      eqToHom (congrArg (fun f : X ⟶ X ↦ (f _*).obj (idealModule i)) hπ) ≫
        idPushforwardHom (idealModule i)

/-- The comparison `π_* Ker(i^♯) ⟶ ℐ` is an isomorphism. -/
instance instIsIso_kernelPushforwardHom {X X' : RingedSpace.{u}} {i : X ⟶ X'}
    [IsFirstOrderThickening i] (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) :
    IsIso (kernelPushforwardHom π hπ) := sorry

/-- Canonical isomorphism `π_* Ker(i^♯) ≅ ℐ`. -/
def kernelPushforwardIso {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
    (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) :
    (π _*).obj (kernelIdealSheaf i) ≅ idealModule i :=
  asIso (kernelPushforwardHom π hπ)

/-- The difference `s - π^♯(i^♯ s)` lies in the sectionwise kernel of `i^♯`. -/
theorem splittingHomSnd_mem {X X' : RingedSpace.{u}} {i : X ⟶ X'}
    [IsFirstOrderThickening i] (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X)
    (U : (Opens X)ᵒᵖ)
    (s : (pushforwardSheaf π).obj.obj U) :
    s - (commRingSheafPushforwardMap π).hom.app U
        ((transportedISharp i π hπ).hom.app U s) ∈
      KernelIdeal.sectionIdeal (commRingSheafPushforwardMap i) (preimageOp π U) := sorry

/-- The kernel coordinate of a section of `π_* 𝒪_{X'}` relative to the splitting `π`. -/
def splittingHomSnd {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
    (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) (U : (Opens X)ᵒᵖ)
    (s : (pushforwardSheaf π).obj.obj U) :
    (idealModule i).val.obj U :=
  (kernelPushforwardIso π hπ).hom.val.app U
    ((KernelIdeal.sectionsIso (commRingSheafPushforwardMap i) (preimageOp π U)).inv
      ⟨s - (commRingSheafPushforwardMap π).hom.app U
          ((transportedISharp i π hπ).hom.app U s),
        splittingHomSnd_mem π hπ U s⟩)

/-- The forward splitting map on sections: `s ↦ (i^♯ s, s - π^♯(i^♯ s))`. -/
def splittingHomApply {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
    (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) (U : (Opens X)ᵒᵖ)
    (s : (pushforwardSheaf π).obj.obj U) :
    (squareZeroSheaf (idealModule i)).obj.obj U :=
  ((transportedISharp i π hπ).hom.app U s, splittingHomSnd π hπ U s)

/-- The forward splitting map preserves zero. -/
theorem splittingHomApply_zero {X X' : RingedSpace.{u}} {i : X ⟶ X'}
    [IsFirstOrderThickening i] (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) (U : (Opens X)ᵒᵖ) :
    splittingHomApply π hπ U 0 = 0 := sorry

/-- The forward splitting map preserves one. -/
theorem splittingHomApply_one {X X' : RingedSpace.{u}} {i : X ⟶ X'}
    [IsFirstOrderThickening i] (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) (U : (Opens X)ᵒᵖ) :
    splittingHomApply π hπ U 1 = 1 := sorry

/-- The forward splitting map preserves addition. -/
theorem splittingHomApply_add {X X' : RingedSpace.{u}} {i : X ⟶ X'}
    [IsFirstOrderThickening i] (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X)
    (U : (Opens X)ᵒᵖ) (s t : (pushforwardSheaf π).obj.obj U) :
    splittingHomApply π hπ U (s + t) =
      splittingHomApply π hπ U s + splittingHomApply π hπ U t := sorry

/-- The forward splitting map preserves multiplication. -/
theorem splittingHomApply_mul {X X' : RingedSpace.{u}} {i : X ⟶ X'}
    [IsFirstOrderThickening i] (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X)
    (U : (Opens X)ᵒᵖ) (s t : (pushforwardSheaf π).obj.obj U) :
    splittingHomApply π hπ U (s * t) =
      splittingHomApply π hπ U s * splittingHomApply π hπ U t := sorry

/-- The component of the forward splitting algebra map over `U`. -/
def splittingHomApp {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
    (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) (U : (Opens X)ᵒᵖ) :
    (pushforwardSheaf π).obj.obj U ⟶ (squareZeroSheaf (idealModule i)).obj.obj U :=
  CommRingCat.ofHom
    { toFun := splittingHomApply π hπ U
      map_zero' := splittingHomApply_zero π hπ U
      map_one' := splittingHomApply_one π hπ U
      map_add' := splittingHomApply_add π hπ U
      map_mul' := splittingHomApply_mul π hπ U }

/-- The components of the forward splitting map commute with restriction. -/
theorem splittingHomApp_naturality {X X' : RingedSpace.{u}} {i : X ⟶ X'}
    [IsFirstOrderThickening i] (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X)
    {U V : (Opens X)ᵒᵖ} (rho : U ⟶ V) :
    (pushforwardSheaf π).obj.map rho ≫ splittingHomApp π hπ V =
      splittingHomApp π hπ U ≫ (squareZeroSheaf (idealModule i)).obj.map rho := sorry

/-- The algebra map `π_* 𝒪_{X'} ⟶ 𝒪_X ⊕ ℐ` sending `s` to `(i^♯ s, s - π^♯(i^♯ s))`. -/
def splittingHom {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
    (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) :
    pushforwardSheaf π ⟶ squareZeroSheaf (idealModule i) :=
  ObjectProperty.homMk
    { app U := splittingHomApp π hπ U
      naturality {_ _} rho := splittingHomApp_naturality π hπ rho }

/-- The inverse splitting map on sections: `(a, x) ↦ π^♯(a) + ι(x)`. -/
def splittingInvApply {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
    (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) (U : (Opens X)ᵒᵖ)
    (x : (squareZeroSheaf (idealModule i)).obj.obj U) :
    (pushforwardSheaf π).obj.obj U :=
  (commRingSheafPushforwardMap π).hom.app U x.1 +
    pushforwardSheafApp π U
      (KernelIdeal.ιApp (commRingSheafPushforwardMap i) (preimageOp π U)
        ((kernelPushforwardIso π hπ).inv.val.app U x.2))

/-- The inverse splitting map preserves zero. -/
theorem splittingInvApply_zero {X X' : RingedSpace.{u}} {i : X ⟶ X'}
    [IsFirstOrderThickening i] (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) (U : (Opens X)ᵒᵖ) :
    splittingInvApply π hπ U 0 = 0 := sorry

/-- The inverse splitting map preserves one. -/
theorem splittingInvApply_one {X X' : RingedSpace.{u}} {i : X ⟶ X'}
    [IsFirstOrderThickening i] (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) (U : (Opens X)ᵒᵖ) :
    splittingInvApply π hπ U 1 = 1 := sorry

/-- The inverse splitting map preserves addition. -/
theorem splittingInvApply_add {X X' : RingedSpace.{u}} {i : X ⟶ X'}
    [IsFirstOrderThickening i] (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X)
    (U : (Opens X)ᵒᵖ) (x y : (squareZeroSheaf (idealModule i)).obj.obj U) :
    splittingInvApply π hπ U (x + y) =
      splittingInvApply π hπ U x + splittingInvApply π hπ U y := sorry

/-- The inverse splitting map preserves multiplication. -/
theorem splittingInvApply_mul {X X' : RingedSpace.{u}} {i : X ⟶ X'}
    [IsFirstOrderThickening i] (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X)
    (U : (Opens X)ᵒᵖ) (x y : (squareZeroSheaf (idealModule i)).obj.obj U) :
    splittingInvApply π hπ U (x * y) =
      splittingInvApply π hπ U x * splittingInvApply π hπ U y := sorry

/-- The component of the inverse splitting algebra map over `U`. -/
def splittingInvApp {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
    (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) (U : (Opens X)ᵒᵖ) :
    (squareZeroSheaf (idealModule i)).obj.obj U ⟶ (pushforwardSheaf π).obj.obj U :=
  CommRingCat.ofHom
    { toFun := splittingInvApply π hπ U
      map_zero' := splittingInvApply_zero π hπ U
      map_one' := splittingInvApply_one π hπ U
      map_add' := splittingInvApply_add π hπ U
      map_mul' := splittingInvApply_mul π hπ U }

/-- The components of the inverse splitting map commute with restriction. -/
theorem splittingInvApp_naturality {X X' : RingedSpace.{u}} {i : X ⟶ X'}
    [IsFirstOrderThickening i] (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X)
    {U V : (Opens X)ᵒᵖ} (rho : U ⟶ V) :
    (squareZeroSheaf (idealModule i)).obj.map rho ≫ splittingInvApp π hπ V =
      splittingInvApp π hπ U ≫ (pushforwardSheaf π).obj.map rho := sorry

/-- The algebra map `𝒪_X ⊕ ℐ ⟶ π_* 𝒪_{X'}` sending `(a, x)` to `π^♯(a) + ι(x)`. -/
def splittingInv {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
    (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) :
    squareZeroSheaf (idealModule i) ⟶ pushforwardSheaf π :=
  ObjectProperty.homMk
    { app U := splittingInvApp π hπ U
      naturality {_ _} rho := splittingInvApp_naturality π hπ rho }

/-- The forward and inverse splitting maps are inverse on the left. -/
theorem splittingHom_comp_splittingInv {X X' : RingedSpace.{u}} {i : X ⟶ X'}
    [IsFirstOrderThickening i] (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) :
    splittingHom π hπ ≫ splittingInv π hπ = 𝟙 (pushforwardSheaf π) := sorry

/-- The forward and inverse splitting maps are inverse on the right. -/
theorem splittingInv_comp_splittingHom {X X' : RingedSpace.{u}} {i : X ⟶ X'}
    [IsFirstOrderThickening i] (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) :
    splittingInv π hπ ≫ splittingHom π hπ =
      𝟙 (squareZeroSheaf (idealModule i)) := sorry

namespace IsFirstOrderThickening

/-- A retraction of a first-order thickening gives a canonical square-zero splitting. -/
noncomputable def splittingIso {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
    (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) :
    pushforwardSheaf π ≅ squareZeroSheaf (idealModule i) where
  hom := splittingHom π hπ
  inv := splittingInv π hπ
  hom_inv_id := splittingHom_comp_splittingInv π hπ
  inv_hom_id := splittingInv_comp_splittingHom π hπ

/-- The algebra projection of the splitting identification is the transported map `i^♯`. -/
theorem splittingIso_fst {X X' : RingedSpace.{u}} {i : X ⟶ X'}
    [IsFirstOrderThickening i] (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) :
    (splittingIso π hπ).hom ≫ SquareZeroSheaf.fst (idealModule i) =
      transportedISharp i π hπ := sorry

/-- The algebra inclusion followed by the inverse splitting map recovers `π^♯`. -/
theorem splittingIso_inl {X X' : RingedSpace.{u}} {i : X ⟶ X'}
    [IsFirstOrderThickening i] (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) :
    SquareZeroSheaf.inl (idealModule i) ≫ (splittingIso π hπ).inv =
      commRingSheafPushforwardMap π := sorry

end IsFirstOrderThickening

end AlgebraicGeometry.RingedSpace
