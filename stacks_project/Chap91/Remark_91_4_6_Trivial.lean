/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.UnderlyingSheaf
public import stacks_project.Chap91.Remark_91_4_5_Trivialization
public import stacks_project.Chap91.Remark_91_4_7_Extension

/-!
# Trivial 08L4 extensions along a chosen trivialization

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

/-- The open of `X` corresponding to an open of `X'` along the thickening homeomorphism `i`. -/
def correspondingOpen (i : X ⟶ X') (U : (Opens X'.carrier)ᵒᵖ) : (Opens X.carrier)ᵒᵖ :=
  op ((Opens.map i.hom.base).obj U.unop)

/-- Inverse image along the trivialization recovers the original open of `X'`. -/
theorem preimageOp_correspondingOpen (τ : Trivialization i) (U : (Opens X'.carrier)ᵒᵖ) :
    preimageOp τ.retraction (correspondingOpen i U) = U := sorry

/-- View a section of `𝒪_{X'}` as a section of `π_* 𝒪_{X'}` over the corresponding open of `X`. -/
def asPushforwardSection (τ : Trivialization i) (U : (Opens X'.carrier)ᵒᵖ)
    (r : X'.sheaf.obj.obj U) :
    (pushforwardSheaf τ.retraction).obj.obj (correspondingOpen i U) :=
  pushforwardSheafApp τ.retraction (correspondingOpen i U)
    (X'.sheaf.obj.map (eqToHom (preimageOp_correspondingOpen τ U).symm) r)

/-- The kernel-ideal coordinate of a section of `𝒪_{X'}`, obtained from `splittingHomSnd`. -/
def splitIdealSection (τ : Trivialization i) (U : (Opens X'.carrier)ᵒᵖ)
    (r : X'.sheaf.obj.obj U) :
    (kernelIdealSheaf i).val.obj U :=
  (kernelIdealSheaf i).val.map (eqToHom (preimageOp_correspondingOpen τ U))
    (hom ((kernelPushforwardIso τ.retraction τ.id).inv.val.app (correspondingOpen i U))
      (splittingHomSnd τ.retraction τ.id (correspondingOpen i U)
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
  sorry

/-- Restriction of the trivial-extension sections preserves addition. -/
theorem trivialRestriction_add (i : X ⟶ X') [IsFirstOrderThickening i] (F K : X.Modules)
    {U V : (Opens X'.carrier)ᵒᵖ} (rho : U ⟶ V) (m n : trivialSection i F K U) :
    trivialRestriction i F K rho (m + n) =
      trivialRestriction i F K rho m + trivialRestriction i F K rho n := sorry

/-- Restriction along an identity morphism is the identity. -/
theorem trivialRestriction_id (i : X ⟶ X') [IsFirstOrderThickening i] (F K : X.Modules)
    (U : (Opens X'.carrier)ᵒᵖ) :
    AddCommGrpCat.ofHom
      { toFun := trivialRestriction i F K (𝟙 U)
        map_zero' := trivialRestriction_zero i F K (𝟙 U)
        map_add' := trivialRestriction_add i F K (𝟙 U) } =
      𝟙 (trivialSection i F K U) := sorry

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
          map_add' := trivialRestriction_add i F K sigma } := sorry

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

/-- Named sectionwise `𝒪_{X'}`-module structure on the product of sections. -/
@[reducible] def instModule_trivialSection (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (U : (Opens X'.carrier)ᵒᵖ) :
    Module (X'.ringCatSheaf.obj.obj U) (trivialSection i F K U) where
  smul := trivialSMul τ c U
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- Restriction of the split action is semilinear over `𝒪_{X'}`. -/
theorem trivial_map_smul (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    {U V : (Opens X'.carrier)ᵒᵖ} (rho : U ⟶ V) (r : X'.sheaf.obj.obj U)
    (m : trivialSection i F K U) :
    trivialRestriction i F K rho (trivialSMul τ c U r m) =
      trivialSMul τ c V (X'.sheaf.obj.map rho r)
        (trivialRestriction i F K rho m) := sorry

/-- The middle `𝒪_{X'}`-module of the trivial 08L4 extension, with underlying abelian sheaf
the product of `i_* ℱ` and `i_* 𝒦` and action from the splitting of `π` together with `c`. -/
def trivialModule (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) : X'.Modules where
  val :=
    @PresheafOfModules.ofPresheaf (Opens X'.carrier) _
      X'.ringCatSheaf.obj (trivialAbelianPresheaf i F K)
      (fun U ↦ instModule_trivialSection τ c U)
      (fun {_ _} rho r m ↦ trivial_map_smul τ c rho r m)
  isSheaf := trivialAbelianPresheaf_isSheaf i F K

/-- Forgetting the `𝒪_{X'}`-action recovers the abelian product of `i_* ℱ` and `i_* 𝒦`. -/
theorem trivialModule_toSheaf (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    (moduleUnderlyingSheaf X').obj (trivialModule τ c) = trivialAbelian i F K := sorry

/-- The inclusion `i_* 𝒦 ⟶ ℱ'_{c,triv}` of the trivial 08L4 sequence. -/
def trivialι (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    (i _*).obj K ⟶ trivialModule τ c where
  val :=
    PresheafOfModules.homMk
      { app U := AddCommGrpCat.ofHom
          { toFun := fun k ↦ ((0 : ((i _*).obj F).val.obj U), k)
            map_zero' := sorry
            map_add' := sorry }
        naturality := sorry }
      sorry

/-- The projection `ℱ'_{c,triv} ⟶ i_* ℱ` of the trivial 08L4 sequence. -/
def trivialπ (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    trivialModule τ c ⟶ (i _*).obj F where
  val :=
    PresheafOfModules.homMk
      { app U := AddCommGrpCat.ofHom
          { toFun := fun m ↦ m.1
            map_zero' := sorry
            map_add' := sorry }
        naturality := sorry }
      sorry

/-- The two maps of the trivial 08L4 sequence compose to zero. -/
theorem trivial_w (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    trivialι τ c ≫ trivialπ τ c = 0 := sorry

/-- The sequence `i_* 𝒦 ⟶ ℱ'_{c,triv} ⟶ i_* ℱ` is short exact. -/
theorem trivial_shortExact (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    (ShortComplex.mk (trivialι τ c) (trivialπ τ c) (trivial_w τ c)).ShortExact := sorry

/-- The infinitesimal map of the trivial sequence equals the prescribed mixed-scalar `c`. -/
theorem trivial_infMap_eq (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    infinitesimalMap i (trivialι τ c) (trivialπ τ c) (trivial_w τ c)
      (trivial_shortExact τ c) = c := sorry

/-- The trivial 08L4 extension of `ℱ` by `𝒦` corresponding to `c` and the trivialization `π`. -/
def trivialExtension (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    InfinitesimalExtension i F K c where
  module := trivialModule τ c
  ι := trivialι τ c
  π := trivialπ τ c
  w := trivial_w τ c
  shortExact := trivial_shortExact τ c
  infMap_eq := trivial_infMap_eq τ c

/-- The packaged trivial extension is short exact. -/
theorem trivialExtension_shortExact (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    (ShortComplex.mk (trivialExtension τ c).ι (trivialExtension τ c).π
      (trivialExtension τ c).w).ShortExact := sorry

/-- The packaged trivial extension has infinitesimal map equal to the prescribed `c`. -/
theorem trivialExtension_infMap (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    infinitesimalMap i (trivialExtension τ c).ι (trivialExtension τ c).π
      (trivialExtension τ c).w (trivialExtension τ c).shortExact = c := sorry

/-- The `𝒪_X`-linear infinitesimal map of the trivial extension recovers `c` after restriction. -/
theorem infMap_restrict_trivial (τ : Trivialization i) {F K : X.Modules}
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    infinitesimalMap_restrict i c =
      infinitesimalMap_restrict i
        (infinitesimalMap i (trivialExtension τ c).ι (trivialExtension τ c).π
          (trivialExtension τ c).w (trivialExtension τ c).shortExact) := sorry

end InfinitesimalExtension
end AlgebraicGeometry.RingedSpace.Modules
