module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Topology.Sheaves.Sheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal.Exact
public import stacks_project.Chap91.Remark_91_10_10_Thickening

/-!
# Relative first-order thickening diagrams of sheaves on a space

After identifying underlying spaces, a first-order thickening of ringed spaces is a same-site
locally surjective square-zero morphism of commutative ring sheaves.  The working form of
equation-huge-2 is a diagram of such sheaves on one space, with front and back solutions and a
given g-map of kernel ideals, but without a filler 𝒪_{X'₁} ⟶ 𝒪_{X'₂}.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.FirstOrderThickening

variable {X : TopCat.{u}}
variable [(Opens.grothendieckTopology X).HasSheafCompose
    (forget₂ CommRingCat.{u} RingCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The kernel ideal of a same-site first-order thickening, as a module over the target ring
sheaf. -/
abbrev ideal {O' O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    (π : O' ⟶ O) [IsFirstOrderThickening π] :=
  SheafOfModules.RingedSite.FirstOrderThickening.ideal π


/-- The underlying additive sheaf map of an `𝒪`-module morphism landing in a restriction of
scalars. -/
def toAdditive {O O' : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    (α : O ⟶ O') {M : SheafOfModules (ringSheaf (Opens.grothendieckTopology X) O)}
    {N : SheafOfModules (ringSheaf (Opens.grothendieckTopology X) O')}
    (φ : M ⟶ (restrictionAlong α).obj N) :
    (SheafOfModules.toSheaf (ringSheaf (Opens.grothendieckTopology X) O)).obj M ⟶
      (SheafOfModules.toSheaf (ringSheaf (Opens.grothendieckTopology X) O')).obj N :=
  (SheafOfModules.toSheaf (ringSheaf (Opens.grothendieckTopology X) O)).map φ ≫
    (SheafOfModules.restrictScalarsCompToSheaf (ringSheafMap α)).hom.app N

variable {OS' OS OX' OX : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- The composite of the kernel inclusion of `πS` with the additive map of `f'` is killed by
the projection of `πX`. -/
theorem kernelMap_lift_zero (πS : OS' ⟶ OS) (f : OS ⟶ OX) (πX : OX' ⟶ OX)
    (f' : OS' ⟶ OX') [IsFirstOrderThickening πS]
    [IsFirstOrderThickening πX] (hcomm : f' ≫ πX = πS ≫ f) :
    (kernel.ι (KernelIdeal.underlyingProjection πS) ≫
        SheafOfModules.unitUnderlyingMap (ringSheafMap f')) ≫
      KernelIdeal.underlyingProjection πX = 0 := sorry

/-- The additive sheaf map of kernel ideals induced by a commutative square of ring sheaves. -/
def kernelAdditiveMap (πS : OS' ⟶ OS) (f : OS ⟶ OX) (πX : OX' ⟶ OX) (f' : OS' ⟶ OX')
    [hπS : IsFirstOrderThickening πS] [hπX : IsFirstOrderThickening πX]
    (hcomm : f' ≫ πX = πS ≫ f) :
    (SheafOfModules.toSheaf (ringSheaf (Opens.grothendieckTopology X) OS)).obj
        (ideal πS) ⟶
      (SheafOfModules.toSheaf (ringSheaf (Opens.grothendieckTopology X) OX)).obj
        (ideal πX) :=
  (hπS.isSquareZero.targetModuleForgetIso inferInstance).hom ≫
    (KernelIdeal.underlyingKernelIso πS).hom ≫
      kernel.lift (KernelIdeal.underlyingProjection πX)
        (kernel.ι (KernelIdeal.underlyingProjection πS) ≫
          SheafOfModules.unitUnderlyingMap (ringSheafMap f'))
        (kernelMap_lift_zero πS f πX f' hcomm) ≫
      (KernelIdeal.underlyingKernelIso πX).inv ≫
        (hπX.isSquareZero.targetModuleForgetIso inferInstance).inv

/-- The `𝒪_S`-module map on kernel ideals induced by a commutative square of ring sheaves. -/
def kernelMap (πS : OS' ⟶ OS) (f : OS ⟶ OX) (πX : OX' ⟶ OX) (f' : OS' ⟶ OX')
    [IsFirstOrderThickening πS] [IsFirstOrderThickening πX]
    (hcomm : f' ≫ πX = πS ≫ f) :
    ideal πS ⟶
      (restrictionAlong f).obj (ideal πX) where
  val :=
    PresheafOfModules.homMk
      ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
        (kernelAdditiveMap πS f πX f' hcomm))
      (fun _ _ _ ↦ sorry)

/-- Forgetting `kernelMap` to additive sheaves recovers `kernelAdditiveMap`. -/
theorem kernelMap_toAdditive (πS : OS' ⟶ OS) (f : OS ⟶ OX) (πX : OX' ⟶ OX)
    (f' : OS' ⟶ OX') [IsFirstOrderThickening πS]
    [IsFirstOrderThickening πX] (hcomm : f' ≫ πX = πS ≫ f) :
    toAdditive f (kernelMap πS f πX f' hcomm) = kernelAdditiveMap πS f πX f' hcomm := sorry

/-- Additive kernel maps of composable commutative squares compose. -/
theorem kernelMap_comp_toAdditive
    {O1' O1 O2' O2 O3' O3 : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    (π1 : O1' ⟶ O1) (π2 : O2' ⟶ O2) (π3 : O3' ⟶ O3)
    [IsFirstOrderThickening π1] [IsFirstOrderThickening π2]
    [IsFirstOrderThickening π3]
    (f12 : O1 ⟶ O2) (f23 : O2 ⟶ O3) (f12' : O1' ⟶ O2') (f23' : O2' ⟶ O3')
    (h12 : f12' ≫ π2 = π1 ≫ f12) (h23 : f23' ≫ π3 = π2 ≫ f23)
    (h13 : (f12' ≫ f23') ≫ π3 = π1 ≫ f12 ≫ f23) :
    toAdditive (f12 ≫ f23) (kernelMap π1 (f12 ≫ f23) π3 (f12' ≫ f23') h13) =
      toAdditive f12 (kernelMap π1 f12 π2 f12' h12) ≫
        toAdditive f23 (kernelMap π2 f23 π3 f23' h23) := sorry

/-- A diagram of first-order thickenings of sheaves of commutative rings on a space, with
front and back solutions and a given g-map of kernel ideals. The morphism
`𝒪_{X'₁} ⟶ 𝒪_{X'₂}` is not part of the data. -/
structure RelativeDiagram
    {OX1 OX1' OS1 OS1' OX2 OX2' OS2 OS2' :
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    (πX1 : OX1' ⟶ OX1) (πS1 : OS1' ⟶ OS1)
    (πX2 : OX2' ⟶ OX2) (πS2 : OS2' ⟶ OS2)
    [IsFirstOrderThickening πX1] [IsFirstOrderThickening πS1]
    [IsFirstOrderThickening πX2] [IsFirstOrderThickening πS2] where
  /-- The structure map `𝒪_{S₁} ⟶ 𝒪_{X₁}`. -/
  f1 : OS1 ⟶ OX1
  /-- The structure map `𝒪_{S'₁} ⟶ 𝒪_{X'₁}`. -/
  f1' : OS1' ⟶ OX1'
  /-- The front solution square commutes. -/
  comm_front : f1' ≫ πX1 = πS1 ≫ f1
  /-- The structure map `𝒪_{S₂} ⟶ 𝒪_{X₂}`. -/
  f2 : OS2 ⟶ OX2
  /-- The structure map `𝒪_{S'₂} ⟶ 𝒪_{X'₂}`. -/
  f2' : OS2' ⟶ OX2'
  /-- The back solution square commutes. -/
  comm_back : f2' ≫ πX2 = πS2 ≫ f2
  /-- The sheaf map `𝒪_{X₁} ⟶ 𝒪_{X₂}` induced by `g`. -/
  g : OX1 ⟶ OX2
  /-- The sheaf map `𝒪_{S₁} ⟶ 𝒪_{S₂}`. -/
  t : OS1 ⟶ OS2
  /-- The sheaf map `𝒪_{S'₁} ⟶ 𝒪_{S'₂}`. -/
  t' : OS1' ⟶ OS2'
  /-- The base thickening square commutes. -/
  comm_S : t' ≫ πS2 = πS1 ≫ t
  /-- The left face on `𝒪_{S₁}`, `𝒪_{X₁}`, `𝒪_{S₂}`, `𝒪_{X₂}` commutes. -/
  comm_X : t ≫ f2 = f1 ≫ g
  /-- The given g-map `𝒢₁ ⟶ 𝒢₂` of kernel ideals. -/
  ν : ideal πX1 ⟶
      (restrictionAlong g).obj (ideal πX2)
  /-- The left kernel square commutes: `c₁` then `ν` equals the kernel map of `t'` then `c₂`. -/
  comm_kernel :
    toAdditive f1 (kernelMap πS1 f1 πX1 f1' comm_front) ≫ toAdditive g ν =
      toAdditive t (kernelMap πS1 t πS2 t' comm_S) ≫
        toAdditive f2 (kernelMap πS2 f2 πX2 f2' comm_back)

namespace RelativeDiagram

variable {OX1 OX1' OS1 OS1' OX2 OX2' OS2 OS2' :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
variable {πX1 : OX1' ⟶ OX1} {πS1 : OS1' ⟶ OS1}
variable {πX2 : OX2' ⟶ OX2} {πS2 : OS2' ⟶ OS2}
variable [IsFirstOrderThickening πX1] [IsFirstOrderThickening πS1]
variable [IsFirstOrderThickening πX2] [IsFirstOrderThickening πS2]

/-- Assemble a relative diagram from its present ring-sheaf maps, face equalities, and the
given g-map of kernel ideals. -/
def of (f1 : OS1 ⟶ OX1) (f1' : OS1' ⟶ OX1')
    (comm_front : f1' ≫ πX1 = πS1 ≫ f1)
    (f2 : OS2 ⟶ OX2) (f2' : OS2' ⟶ OX2')
    (comm_back : f2' ≫ πX2 = πS2 ≫ f2)
    (g : OX1 ⟶ OX2) (t : OS1 ⟶ OS2) (t' : OS1' ⟶ OS2')
    (comm_S : t' ≫ πS2 = πS1 ≫ t) (comm_X : t ≫ f2 = f1 ≫ g)
    (ν : ideal πX1 ⟶
      (restrictionAlong g).obj (ideal πX2))
    (comm_kernel :
      toAdditive f1 (kernelMap πS1 f1 πX1 f1' comm_front) ≫ toAdditive g ν =
        toAdditive t (kernelMap πS1 t πS2 t' comm_S) ≫
          toAdditive f2 (kernelMap πS2 f2 πX2 f2' comm_back)) :
    RelativeDiagram πX1 πS1 πX2 πS2 where
  f1 := f1
  f1' := f1'
  comm_front := comm_front
  f2 := f2
  f2' := f2'
  comm_back := comm_back
  g := g
  t := t
  t' := t'
  comm_S := comm_S
  comm_X := comm_X
  ν := ν
  comm_kernel := comm_kernel

/-- The present ring-sheaf faces of a relative diagram commute. -/
theorem spec (D : RelativeDiagram πX1 πS1 πX2 πS2) :
    D.f1' ≫ πX1 = πS1 ≫ D.f1 ∧ D.f2' ≫ πX2 = πS2 ≫ D.f2 ∧
      D.t' ≫ πS2 = πS1 ≫ D.t ∧ D.t ≫ D.f2 = D.f1 ≫ D.g := sorry

/-- The left kernel square of a relative diagram commutes. -/
theorem spec_kernel (D : RelativeDiagram πX1 πS1 πX2 πS2) :
    toAdditive D.f1 (kernelMap πS1 D.f1 πX1 D.f1' D.comm_front) ≫ toAdditive D.g D.ν =
      toAdditive D.t (kernelMap πS1 D.t πS2 D.t' D.comm_S) ≫
        toAdditive D.f2 (kernelMap πS2 D.f2 πX2 D.f2' D.comm_back) := sorry

/-- The front solution square. -/
theorem frontSq (D : RelativeDiagram πX1 πS1 πX2 πS2) : CommSq D.f1' πS1 πX1 D.f1 := sorry

/-- The back solution square. -/
theorem backSq (D : RelativeDiagram πX1 πS1 πX2 πS2) : CommSq D.f2' πS2 πX2 D.f2 := sorry

/-- The vertical map `c₁ : 𝒥₁ ⟶ 𝒢₁` induced by `f'₁`. -/
def c (D : RelativeDiagram πX1 πS1 πX2 πS2) :
    ideal πS1 ⟶
      (restrictionAlong D.f1).obj (ideal πX1) :=
  kernelMap πS1 D.f1 πX1 D.f1' D.comm_front

/-- The vertical map `c₂ : 𝒥₂ ⟶ 𝒢₂` induced by `f'₂`. -/
def c_back (D : RelativeDiagram πX1 πS1 πX2 πS2) :
    ideal πS2 ⟶
      (restrictionAlong D.f2).obj (ideal πX2) :=
  kernelMap πS2 D.f2 πX2 D.f2' D.comm_back

/-- Forgetting `c` to additive sheaves recovers the additive kernel map of `f'₁`. -/
theorem c_toAdditive (D : RelativeDiagram πX1 πS1 πX2 πS2) :
    toAdditive D.f1 (c D) = kernelAdditiveMap πS1 D.f1 πX1 D.f1' D.comm_front := sorry

/-- Forgetting `c_back` to additive sheaves recovers the additive kernel map of `f'₂`. -/
theorem c_back_toAdditive (D : RelativeDiagram πX1 πS1 πX2 πS2) :
    toAdditive D.f2 (c_back D) = kernelAdditiveMap πS2 D.f2 πX2 D.f2' D.comm_back := sorry

/-- A morphism `φ : 𝒪_{X'₁} ⟶ 𝒪_{X'₂}` fits the diagram if the two present faces through
`φ` commute and `φ` induces the given g-map `ν` on kernel ideals. -/
def Fits (D : RelativeDiagram πX1 πS1 πX2 πS2) (φ : OX1' ⟶ OX2') : Prop :=
  φ ≫ πX2 = πX1 ≫ D.g ∧ D.t' ≫ D.f2' = D.f1' ≫ φ ∧
    ∀ hπ : φ ≫ πX2 = πX1 ≫ D.g, kernelMap πX1 D.g πX2 φ hπ = D.ν

/-- Fitting a diagram is commutativity of the two present faces through `φ` together with
inducing `ν` on kernels. -/
theorem fits_iff (D : RelativeDiagram πX1 πS1 πX2 πS2) (φ : OX1' ⟶ OX2') :
    Fits D φ ↔
      φ ≫ πX2 = πX1 ≫ D.g ∧ D.t' ≫ D.f2' = D.f1' ≫ φ ∧
        ∀ hπ : φ ≫ πX2 = πX1 ≫ D.g, kernelMap πX1 D.g πX2 φ hπ = D.ν := sorry

/-- A fitting map is compatible with the thickenings `π_{Xⱼ}`. -/
theorem fits_comm_π (D : RelativeDiagram πX1 πS1 πX2 πS2) {φ : OX1' ⟶ OX2'}
    (h : Fits D φ) : φ ≫ πX2 = πX1 ≫ D.g := sorry

/-- A fitting map is compatible with the structure maps `f'ⱼ`. -/
theorem fits_comm_f' (D : RelativeDiagram πX1 πS1 πX2 πS2) {φ : OX1' ⟶ OX2'}
    (h : Fits D φ) : D.t' ≫ D.f2' = D.f1' ≫ φ := sorry

/-- A fitting map induces the given g-map of kernel ideals. -/
theorem fits_induces (D : RelativeDiagram πX1 πS1 πX2 πS2) {φ : OX1' ⟶ OX2'}
    (h : Fits D φ) (hπ : φ ≫ πX2 = πX1 ≫ D.g) :
    kernelMap πX1 D.g πX2 φ hπ = D.ν := sorry

/-- The front row `0 ⟶ 𝒢₁ ⟶ 𝒪_{X'₁} ⟶ 𝒪_{X₁} ⟶ 0` is short exact. -/
theorem row_front_X_shortExact (D : RelativeDiagram πX1 πS1 πX2 πS2) :
    (KernelIdeal.underlyingShortComplex πX1).ShortExact := sorry

/-- The front base row `0 ⟶ 𝒥₁ ⟶ 𝒪_{S'₁} ⟶ 𝒪_{S₁} ⟶ 0` is short exact. -/
theorem row_front_S_shortExact (D : RelativeDiagram πX1 πS1 πX2 πS2) :
    (KernelIdeal.underlyingShortComplex πS1).ShortExact := sorry

/-- The back row `0 ⟶ 𝒢₂ ⟶ 𝒪_{X'₂} ⟶ 𝒪_{X₂} ⟶ 0` is short exact. -/
theorem row_back_X_shortExact (D : RelativeDiagram πX1 πS1 πX2 πS2) :
    (KernelIdeal.underlyingShortComplex πX2).ShortExact := sorry

/-- The back base row `0 ⟶ 𝒥₂ ⟶ 𝒪_{S'₂} ⟶ 𝒪_{S₂} ⟶ 0` is short exact. -/
theorem row_back_S_shortExact (D : RelativeDiagram πX1 πS1 πX2 πS2) :
    (KernelIdeal.underlyingShortComplex πS2).ShortExact := sorry

end RelativeDiagram

end TopCat.Sheaf.FirstOrderThickening
