/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.UnderlyingSheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Trivialization
public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension

/-!
# Trivial infinitesimal extensions along a chosen trivialization

On a first-order thickening with a chosen left inverse, a mixed-scalar infinitesimal map
`c` determines an `𝒪_{X'}`-module structure on the objectwise product of `i_* ℱ` and
`i_* 𝒦`, using the algebra splitting `π_* 𝒪_{X'} ≅ 𝒪_X ⊕ ℐ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ConcreteCategory CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules
namespace InfinitesimalExtension

variable {X X' : RingedSpace.{u}}
variable {i : X ⟶ X'} [IsFirstOrderThickening i]

/-- Inverse image along the trivialization recovers the original open of `X'`. -/
theorem preimageOp_retraction (τ : Trivialization i) (U : (Opens X'.carrier)ᵒᵖ) :
    preimageOp τ.retraction (preimageOp i U) = U := sorry

-- The exposed scalar-coordinate construction must retain access to its private transport
-- implementation without adding that implementation to the public mathematical API.
set_option backward.privateInPublic true in
/-- View a section of `𝒪_{X'}` as a section of `π_* 𝒪_{X'}` over the corresponding open of `X`. -/
private def asPushforwardSection (τ : Trivialization i) (U : (Opens X'.carrier)ᵒᵖ)
    (r : X'.sheaf.obj.obj U) :
    (pushforwardSheaf τ.retraction).obj.obj (preimageOp i U) :=
  pushforwardSheafApp τ.retraction (preimageOp i U)
    (X'.sheaf.obj.map (eqToHom (preimageOp_retraction τ U).symm) r)

set_option backward.privateInPublic true in
/-- The kernel-ideal coordinate of a section of `𝒪_{X'}`, obtained from `splittingHomSnd`. -/
def splitIdealSection (τ : Trivialization i) (U : (Opens X'.carrier)ᵒᵖ)
    (r : X'.sheaf.obj.obj U) :
    (kernelIdealSheaf i).val.obj U :=
  (kernelIdealSheaf i).val.map (eqToHom (preimageOp_retraction τ U))
    (hom ((kernelPushforwardIso τ.retraction τ.id).inv.val.app (preimageOp i U))
      (splittingHomSnd τ.retraction τ.id (preimageOp i U)
        (asPushforwardSection τ U r)))

/-- Objectwise sections of the underlying abelian sheaf of the trivial extension. -/
def trivialSection (i : X ⟶ X') [IsFirstOrderThickening i] (F K : X.Modules)
    (U : (Opens X'.carrier)ᵒᵖ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (((i _*).obj F).val.obj U × ((i _*).obj K).val.obj U)

/-- Restriction of a pair of sections of `i_* ℱ` and `i_* 𝒦`. -/
def trivialRestriction (i : X ⟶ X') [IsFirstOrderThickening i] (F K : X.Modules)
    {U V : (Opens X'.carrier)ᵒᵖ} (rho : U ⟶ V) (m : trivialSection i F K U) :
    trivialSection i F K V :=
  (((i _*).obj F).val.map rho m.1, ((i _*).obj K).val.map rho m.2)

/-- Restriction of the trivial-extension sections preserves zero. -/
theorem trivialRestriction_zero (i : X ⟶ X') [IsFirstOrderThickening i] (F K : X.Modules)
    {U V : (Opens X'.carrier)ᵒᵖ} (rho : U ⟶ V) :
    trivialRestriction i F K rho (0 : trivialSection i F K U) = (0 : trivialSection i F K V) :=
  by
    exact Prod.ext
      (map_zero (((i _*).obj F).val.map rho).hom)
      (map_zero (((i _*).obj K).val.map rho).hom)

/-- Restriction of the trivial-extension sections preserves addition. -/
theorem trivialRestriction_add (i : X ⟶ X') [IsFirstOrderThickening i] (F K : X.Modules)
    {U V : (Opens X'.carrier)ᵒᵖ} (rho : U ⟶ V) (m n : trivialSection i F K U) :
    trivialRestriction i F K rho (m + n) =
      trivialRestriction i F K rho m + trivialRestriction i F K rho n := by
  exact Prod.ext
    (map_add (((i _*).obj F).val.map rho).hom m.1 n.1)
    (map_add (((i _*).obj K).val.map rho).hom m.2 n.2)

/-- Restriction along an identity morphism is the identity. -/
theorem trivialRestriction_id (i : X ⟶ X') [IsFirstOrderThickening i] (F K : X.Modules)
    (U : (Opens X'.carrier)ᵒᵖ) :
    AddCommGrpCat.ofHom
      { toFun := trivialRestriction i F K (𝟙 U)
        map_zero' := trivialRestriction_zero i F K (𝟙 U)
        map_add' := trivialRestriction_add i F K (𝟙 U) } =
      𝟙 (trivialSection i F K U) := by
  ext m
  simp [trivialRestriction]

/-- Restriction along a composite morphism is the composite restriction. -/
theorem trivialRestriction_comp (i : X ⟶ X') [IsFirstOrderThickening i] (F K : X.Modules)
    {U V W : (Opens X'.carrier)ᵒᵖ} (rho : U ⟶ V) (sigma : V ⟶ W) :
    AddCommGrpCat.ofHom
      { toFun := trivialRestriction i F K (rho ≫ sigma)
        map_zero' := trivialRestriction_zero i F K (rho ≫ sigma)
        map_add' := trivialRestriction_add i F K (rho ≫ sigma) } =
      AddCommGrpCat.ofHom
        { toFun := trivialRestriction i F K rho
          map_zero' := trivialRestriction_zero i F K rho
          map_add' := trivialRestriction_add i F K rho } ≫
      AddCommGrpCat.ofHom
        { toFun := trivialRestriction i F K sigma
          map_zero' := trivialRestriction_zero i F K sigma
          map_add' := trivialRestriction_add i F K sigma } := by
  ext m
  simp [trivialRestriction]

/-- The abelian presheaf of objectwise products of sections of `i_* ℱ` and `i_* 𝒦`. -/
def trivialAbelianPresheaf (i : X ⟶ X') [IsFirstOrderThickening i] (F K : X.Modules) :
    (Opens X'.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := trivialSection i F K U
  map rho := AddCommGrpCat.ofHom
    { toFun := trivialRestriction i F K rho
      map_zero' := trivialRestriction_zero i F K rho
      map_add' := trivialRestriction_add i F K rho }
  map_id U := trivialRestriction_id i F K U
  map_comp rho sigma := trivialRestriction_comp i F K rho sigma

/-- The objectwise product of sheaves of abelian groups is a sheaf. -/
theorem trivialAbelianPresheaf_isSheaf (i : X ⟶ X') [IsFirstOrderThickening i] (F K : X.Modules) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X'.carrier)
      (trivialAbelianPresheaf i F K) := sorry

/-- The underlying abelian sheaf of the trivial extension, as the product of `i_* ℱ` and `i_* 𝒦`. -/
def trivialAbelian (i : X ⟶ X') [IsFirstOrderThickening i] (F K : X.Modules) :
    X'.carrier.Sheaf AddCommGrpCat.{u} :=
  ⟨trivialAbelianPresheaf i F K, trivialAbelianPresheaf_isSheaf i F K⟩

/-- The `ℐ`-correction `c(x ⊗ f)` attached to the kernel coordinate of a scalar. -/
def trivialCorrection (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (U : (Opens X'.carrier)ᵒᵖ) (r : X'.sheaf.obj.obj U)
    (f : ((i _*).obj F).val.obj U) :
    ((i _*).obj K).val.obj U :=
  hom (c.val.app U) (tensorSection X'.sheaf U (splitIdealSection τ U r) f)

/-- Scalar multiplication on pairs of sections, using the splitting of `π_* 𝒪_{X'}` and `c`. -/
def trivialSMul (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (U : (Opens X'.carrier)ᵒᵖ) (r : X'.sheaf.obj.obj U)
    (m : trivialSection i F K U) : trivialSection i F K U :=
  (r • m.1, r • m.2 + trivialCorrection τ c U r m.1)

/-- The objectwise action on a pair is the split formula `(a • f, a • k + c(x ⊗ f))`. -/
theorem trivialSMul_spec (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (U : (Opens X'.carrier)ᵒᵖ) (r : X'.sheaf.obj.obj U)
    (f : ((i _*).obj F).val.obj U) (k : ((i _*).obj K).val.obj U) :
    trivialSMul τ c U r (f, k) =
      (r • f, r • k + trivialCorrection τ c U r f) :=
  rfl

/-- The split scalar action satisfies the six axioms of a module action. -/
theorem trivialSMul_laws (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (U : (Opens X'.carrier)ᵒᵖ) :
    (∀ m, trivialSMul τ c U 1 m = m) ∧
    (∀ r s m, trivialSMul τ c U (r * s) m =
      trivialSMul τ c U r (trivialSMul τ c U s m)) ∧
    (∀ r, trivialSMul τ c U r 0 = 0) ∧
    (∀ r m n, trivialSMul τ c U r (m + n) =
      trivialSMul τ c U r m + trivialSMul τ c U r n) ∧
    (∀ r s m, trivialSMul τ c U (r + s) m =
      trivialSMul τ c U r m + trivialSMul τ c U s m) ∧
    (∀ m, trivialSMul τ c U 0 m = 0) := sorry

/-- The split action equips the product of section groups with a module structure. -/
@[reducible] def trivialSectionModule (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (U : (Opens X'.carrier)ᵒᵖ) :
    Module (X'.ringCatSheaf.obj.obj U) (trivialSection i F K U) where
  smul := trivialSMul τ c U
  one_smul := (trivialSMul_laws τ c U).1
  mul_smul := (trivialSMul_laws τ c U).2.1
  smul_zero := (trivialSMul_laws τ c U).2.2.1
  smul_add := (trivialSMul_laws τ c U).2.2.2.1
  add_smul := (trivialSMul_laws τ c U).2.2.2.2.1
  zero_smul := (trivialSMul_laws τ c U).2.2.2.2.2

/-- Restriction of the split action is semilinear over `𝒪_{X'}`. -/
theorem trivial_map_smul (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    {U V : (Opens X'.carrier)ᵒᵖ} (rho : U ⟶ V) (r : X'.sheaf.obj.obj U)
    (m : trivialSection i F K U) :
    trivialRestriction i F K rho (trivialSMul τ c U r m) =
      trivialSMul τ c V (X'.sheaf.obj.map rho r)
        (trivialRestriction i F K rho m) := sorry

/-- The middle `𝒪_{X'}`-module of the trivial infinitesimal extension, with underlying abelian sheaf
the product of `i_* ℱ` and `i_* 𝒦` and action from the splitting of `π` together with `c`. -/
def trivialModule (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) : X'.Modules where
  val :=
    @PresheafOfModules.ofPresheaf (Opens X'.carrier) _
      X'.ringCatSheaf.obj (trivialAbelianPresheaf i F K)
      (fun U ↦ trivialSectionModule τ c U)
      (fun {_ _} rho r m ↦ trivial_map_smul τ c rho r m)
  isSheaf := trivialAbelianPresheaf_isSheaf i F K

/-- Forgetting the `𝒪_{X'}`-action recovers the abelian product of `i_* ℱ` and `i_* 𝒦`. -/
theorem trivialModule_toSheaf (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    (moduleUnderlyingSheaf X').obj (trivialModule τ c) = trivialAbelian i F K := rfl

/-- The inclusion `i_* 𝒦 ⟶ ℱ'_{c,triv}` of the trivial infinitesimal sequence. -/
def trivialι (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    (i _*).obj K ⟶ trivialModule τ c where
  val :=
    PresheafOfModules.homMk
      { app U := AddCommGrpCat.ofHom
          { toFun := fun k ↦ ((0 : ((i _*).obj F).val.obj U), k)
            map_zero' := rfl
            map_add' := by intro a b; exact Prod.ext (zero_add 0).symm rfl }
        naturality := by
          intro U V rho
          apply ConcreteCategory.hom_ext
          intro k
          apply Prod.ext
          · exact (map_zero (((i _*).obj F).val.map rho).hom).symm
          · rfl }
      (by
        intro U r k
        change (0, r • k) =
          (r • (0 : ((i _*).obj F).val.obj U),
            r • k + trivialCorrection τ c U r 0)
        have h : trivialCorrection τ c U r 0 = 0 := by
          unfold trivialCorrection
          change hom (c.val.app U)
            ((tensorSectionRight X'.sheaf U (splitIdealSection τ U r)) 0) = 0
          rw [map_zero, map_zero]
        simp [h])

/-- The projection `ℱ'_{c,triv} ⟶ i_* ℱ` of the trivial infinitesimal sequence. -/
def trivialπ (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    trivialModule τ c ⟶ (i _*).obj F where
  val :=
    PresheafOfModules.homMk
      { app U := AddCommGrpCat.ofHom
          { toFun := fun m ↦ m.1
            map_zero' := rfl
            map_add' := by intro a b; rfl }
        naturality := by intros; rfl }
      (by intros; rfl)

/-- The two maps of the trivial infinitesimal sequence compose to zero. -/
theorem trivial_w (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    trivialι τ c ≫ trivialπ τ c = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext k
  rfl

/-- The sequence `i_* 𝒦 ⟶ ℱ'_{c,triv} ⟶ i_* ℱ` is short exact. -/
theorem trivial_shortExact (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    (ShortComplex.mk (trivialι τ c) (trivialπ τ c) (trivial_w τ c)).ShortExact := sorry

/-- The infinitesimal map of the trivial sequence equals the prescribed mixed-scalar `c`. -/
theorem trivial_infMap_eq (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    infinitesimalMap i (trivialι τ c) (trivialπ τ c) (trivial_w τ c)
      (trivial_shortExact τ c) = c := sorry

/-- The trivial infinitesimal extension of `ℱ` by `𝒦` corresponding to `c` and the trivialization `π`. -/
def trivialExtension (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    InfinitesimalExtension i F K c where
  module := trivialModule τ c
  ι := trivialι τ c
  π := trivialπ τ c
  w := trivial_w τ c
  shortExact := trivial_shortExact τ c
  infMap_eq := trivial_infMap_eq τ c

end InfinitesimalExtension
end AlgebraicGeometry.RingedSpace.Modules
