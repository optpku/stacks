/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal.Exact
public import stacks_project.Chap91.Remark_91_10_10_Thickening

/-!
# Relative first-order thickening diagrams of sheaves on a site

After identifying underlying topoi, a first-order thickening of ringed topoi is a same-site
locally surjective square-zero morphism of commutative ring sheaves.  The working form of
equation-huge-2-ringed-topoi is a diagram of such sheaves on one site, with front and back
solutions and a given g-map of kernel ideals, but without a filler 𝒪'₁ ⟶ 𝒪'₂.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The underlying additive sheaf map of an 𝒪-module morphism landing in a restriction of
scalars. -/
def toAdditive {O O' : Sheaf J CommRingCat.{max u v}} (α : O ⟶ O')
    {M : SheafOfModules (ringSheaf J O)} {N : SheafOfModules (ringSheaf J O')}
    (φ : M ⟶ (restrictionAlong α).obj N) :
    (SheafOfModules.toSheaf (ringSheaf J O)).obj M ⟶
      (SheafOfModules.toSheaf (ringSheaf J O')).obj N :=
  (SheafOfModules.toSheaf (ringSheaf J O)).map φ ≫
    (SheafOfModules.restrictScalarsCompToSheaf (ringSheafMap α)).hom.app N

variable {OB' OB O' O : Sheaf J CommRingCat.{max u v}}

/-- The composite of the kernel inclusion of `πB` with the additive map of `f'` is killed by
the projection of `πO`. -/
theorem inducedKernelMap_lift_zero (πB : OB' ⟶ OB) (f : OB ⟶ O) (πO : O' ⟶ O)
    (f' : OB' ⟶ O') [IsFirstOrderThickening πB] [IsFirstOrderThickening πO]
    (hcomm : f' ≫ πO = πB ≫ f) :
    (kernel.ι (KernelIdeal.underlyingProjection πB) ≫
        SheafOfModules.unitUnderlyingMap (ringSheafMap f')) ≫
      KernelIdeal.underlyingProjection πO = 0 := sorry

/-- The additive sheaf map of kernel ideals induced by a commutative square of ring sheaves. -/
def inducedKernelAdditiveMap (πB : OB' ⟶ OB) (f : OB ⟶ O) (πO : O' ⟶ O) (f' : OB' ⟶ O')
    [hπB : IsFirstOrderThickening πB] [hπO : IsFirstOrderThickening πO]
    (hcomm : f' ≫ πO = πB ≫ f) :
    (SheafOfModules.toSheaf (ringSheaf J OB)).obj (ideal πB) ⟶
      (SheafOfModules.toSheaf (ringSheaf J O)).obj (ideal πO) :=
  (hπB.isSquareZero.targetModuleForgetIso inferInstance).hom ≫
    (KernelIdeal.underlyingKernelIso πB).hom ≫
      kernel.lift (KernelIdeal.underlyingProjection πO)
        (kernel.ι (KernelIdeal.underlyingProjection πB) ≫
          SheafOfModules.unitUnderlyingMap (ringSheafMap f'))
        (inducedKernelMap_lift_zero πB f πO f' hcomm) ≫
      (KernelIdeal.underlyingKernelIso πO).inv ≫
        (hπO.isSquareZero.targetModuleForgetIso inferInstance).inv

/-- The 𝒪_B-module map on kernel ideals induced by a commutative square of ring sheaves. -/
def inducedKernelMap (πB : OB' ⟶ OB) (f : OB ⟶ O) (πO : O' ⟶ O) (f' : OB' ⟶ O')
    [IsFirstOrderThickening πB] [IsFirstOrderThickening πO]
    (hcomm : f' ≫ πO = πB ≫ f) :
    ideal πB ⟶ (restrictionAlong f).obj (ideal πO) where
  val :=
    PresheafOfModules.homMk
      ((sheafToPresheaf J AddCommGrpCat.{max u v}).map
        (inducedKernelAdditiveMap πB f πO f' hcomm))
      (fun _ _ _ ↦ sorry)

/-- Forgetting `inducedKernelMap` to additive sheaves recovers `inducedKernelAdditiveMap`. -/
theorem inducedKernelMap_toAdditive (πB : OB' ⟶ OB) (f : OB ⟶ O) (πO : O' ⟶ O)
    (f' : OB' ⟶ O') [IsFirstOrderThickening πB] [IsFirstOrderThickening πO]
    (hcomm : f' ≫ πO = πB ≫ f) :
    toAdditive f (inducedKernelMap πB f πO f' hcomm) =
      inducedKernelAdditiveMap πB f πO f' hcomm := sorry

/-- Additive kernel maps of composable commutative squares compose. -/
theorem inducedKernelMap_comp_toAdditive
    {O1' O1 O2' O2 O3' O3 : Sheaf J CommRingCat.{max u v}}
    (π1 : O1' ⟶ O1) (π2 : O2' ⟶ O2) (π3 : O3' ⟶ O3)
    [IsFirstOrderThickening π1] [IsFirstOrderThickening π2] [IsFirstOrderThickening π3]
    (f12 : O1 ⟶ O2) (f23 : O2 ⟶ O3) (f12' : O1' ⟶ O2') (f23' : O2' ⟶ O3')
    (h12 : f12' ≫ π2 = π1 ≫ f12) (h23 : f23' ≫ π3 = π2 ≫ f23)
    (h13 : (f12' ≫ f23') ≫ π3 = π1 ≫ f12 ≫ f23) :
    toAdditive (f12 ≫ f23) (inducedKernelMap π1 (f12 ≫ f23) π3 (f12' ≫ f23') h13) =
      toAdditive f12 (inducedKernelMap π1 f12 π2 f12' h12) ≫
        toAdditive f23 (inducedKernelMap π2 f23 π3 f23' h23) := sorry

/-- A diagram of first-order thickenings of sheaves of commutative rings on a site, with
front and back solutions and a given g-map of kernel ideals. The morphism 𝒪'₁ ⟶ 𝒪'₂ is
not part of the data. -/
structure RelativeDiagram
    {O1 O1' OB1 OB1' O2 O2' OB2 OB2' : Sheaf J CommRingCat.{max u v}}
    (πO1 : O1' ⟶ O1) (πB1 : OB1' ⟶ OB1) (πO2 : O2' ⟶ O2) (πB2 : OB2' ⟶ OB2)
    [IsFirstOrderThickening πO1] [IsFirstOrderThickening πB1]
    [IsFirstOrderThickening πO2] [IsFirstOrderThickening πB2] where
  /-- The structure map 𝒪_{B₁} ⟶ 𝒪₁. -/
  f1 : OB1 ⟶ O1
  /-- The structure map 𝒪_{B'₁} ⟶ 𝒪'₁. -/
  f1' : OB1' ⟶ O1'
  /-- The front solution square commutes. -/
  comm_front : f1' ≫ πO1 = πB1 ≫ f1
  /-- The structure map 𝒪_{B₂} ⟶ 𝒪₂. -/
  f2 : OB2 ⟶ O2
  /-- The structure map 𝒪_{B'₂} ⟶ 𝒪'₂. -/
  f2' : OB2' ⟶ O2'
  /-- The back solution square commutes. -/
  comm_back : f2' ≫ πO2 = πB2 ≫ f2
  /-- The sheaf map 𝒪₁ ⟶ 𝒪₂ induced by g. -/
  g : O1 ⟶ O2
  /-- The sheaf map 𝒪_{B₁} ⟶ 𝒪_{B₂}. -/
  t : OB1 ⟶ OB2
  /-- The sheaf map 𝒪_{B'₁} ⟶ 𝒪_{B'₂}. -/
  t' : OB1' ⟶ OB2'
  /-- The base thickening square commutes. -/
  comm_B : t' ≫ πB2 = πB1 ≫ t
  /-- The left face on 𝒪_{B₁}, 𝒪₁, 𝒪_{B₂}, 𝒪₂ commutes. -/
  comm_O : t ≫ f2 = f1 ≫ g
  /-- The given g-map 𝒢₁ ⟶ 𝒢₂ of kernel ideals. -/
  ν : ideal πO1 ⟶ (restrictionAlong g).obj (ideal πO2)
  /-- The left kernel square commutes: c₁ then ν equals the kernel map of t' then c₂. -/
  comm_kernel :
    toAdditive f1 (inducedKernelMap πB1 f1 πO1 f1' comm_front) ≫ toAdditive g ν =
      toAdditive t (inducedKernelMap πB1 t πB2 t' comm_B) ≫
        toAdditive f2 (inducedKernelMap πB2 f2 πO2 f2' comm_back)

namespace RelativeDiagram

variable {O1 O1' OB1 OB1' O2 O2' OB2 OB2' : Sheaf J CommRingCat.{max u v}}
variable {πO1 : O1' ⟶ O1} {πB1 : OB1' ⟶ OB1}
variable {πO2 : O2' ⟶ O2} {πB2 : OB2' ⟶ OB2}
variable [IsFirstOrderThickening πO1] [IsFirstOrderThickening πB1]
variable [IsFirstOrderThickening πO2] [IsFirstOrderThickening πB2]

/-- Assemble a relative diagram from its present ring-sheaf maps, face equalities, and the
given g-map of kernel ideals. -/
def of (f1 : OB1 ⟶ O1) (f1' : OB1' ⟶ O1') (comm_front : f1' ≫ πO1 = πB1 ≫ f1)
    (f2 : OB2 ⟶ O2) (f2' : OB2' ⟶ O2') (comm_back : f2' ≫ πO2 = πB2 ≫ f2)
    (g : O1 ⟶ O2) (t : OB1 ⟶ OB2) (t' : OB1' ⟶ OB2')
    (comm_B : t' ≫ πB2 = πB1 ≫ t) (comm_O : t ≫ f2 = f1 ≫ g)
    (ν : ideal πO1 ⟶ (restrictionAlong g).obj (ideal πO2))
    (comm_kernel :
      toAdditive f1 (inducedKernelMap πB1 f1 πO1 f1' comm_front) ≫ toAdditive g ν =
        toAdditive t (inducedKernelMap πB1 t πB2 t' comm_B) ≫
          toAdditive f2 (inducedKernelMap πB2 f2 πO2 f2' comm_back)) :
    RelativeDiagram πO1 πB1 πO2 πB2 where
  f1 := f1
  f1' := f1'
  comm_front := comm_front
  f2 := f2
  f2' := f2'
  comm_back := comm_back
  g := g
  t := t
  t' := t'
  comm_B := comm_B
  comm_O := comm_O
  ν := ν
  comm_kernel := comm_kernel

/-- The present faces of a relative diagram commute. -/
theorem spec (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    D.f1' ≫ πO1 = πB1 ≫ D.f1 ∧ D.f2' ≫ πO2 = πB2 ≫ D.f2 ∧
      D.t' ≫ πB2 = πB1 ≫ D.t ∧ D.t ≫ D.f2 = D.f1 ≫ D.g := sorry

/-- The left kernel square of a relative diagram commutes. -/
theorem spec_kernel (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    toAdditive D.f1 (inducedKernelMap πB1 D.f1 πO1 D.f1' D.comm_front) ≫
        toAdditive D.g D.ν =
      toAdditive D.t (inducedKernelMap πB1 D.t πB2 D.t' D.comm_B) ≫
        toAdditive D.f2 (inducedKernelMap πB2 D.f2 πO2 D.f2' D.comm_back) := sorry

/-- The front solution square. -/
theorem frontSq (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    CommSq D.f1' πB1 πO1 D.f1 := sorry

/-- The back solution square. -/
theorem backSq (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    CommSq D.f2' πB2 πO2 D.f2 := sorry

/-- The vertical map c₁ : 𝒥₁ ⟶ 𝒢₁ induced by f'₁. -/
def c (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    ideal πB1 ⟶ (restrictionAlong D.f1).obj (ideal πO1) :=
  inducedKernelMap πB1 D.f1 πO1 D.f1' D.comm_front

/-- The vertical map c₂ : 𝒥₂ ⟶ 𝒢₂ induced by f'₂. -/
def c_back (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    ideal πB2 ⟶ (restrictionAlong D.f2).obj (ideal πO2) :=
  inducedKernelMap πB2 D.f2 πO2 D.f2' D.comm_back

/-- Forgetting `c` to additive sheaves recovers the additive kernel map of f'₁. -/
theorem c_toAdditive (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    toAdditive D.f1 (c D) =
      inducedKernelAdditiveMap πB1 D.f1 πO1 D.f1' D.comm_front := sorry

/-- Forgetting `c_back` to additive sheaves recovers the additive kernel map of f'₂. -/
theorem c_back_toAdditive (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    toAdditive D.f2 (c_back D) =
      inducedKernelAdditiveMap πB2 D.f2 πO2 D.f2' D.comm_back := sorry

/-- A morphism φ : 𝒪'₁ ⟶ 𝒪'₂ fits the diagram if the two present faces through φ commute
and φ induces the given g-map ν on kernel ideals. -/
def Fits (D : RelativeDiagram πO1 πB1 πO2 πB2) (φ : O1' ⟶ O2') : Prop :=
  φ ≫ πO2 = πO1 ≫ D.g ∧ D.t' ≫ D.f2' = D.f1' ≫ φ ∧
    ∀ hπ : φ ≫ πO2 = πO1 ≫ D.g, inducedKernelMap πO1 D.g πO2 φ hπ = D.ν

/-- Fitting a diagram is commutativity of the two present faces through φ together with
inducing ν on kernels. -/
theorem fits_iff (D : RelativeDiagram πO1 πB1 πO2 πB2) (φ : O1' ⟶ O2') :
    Fits D φ ↔
      φ ≫ πO2 = πO1 ≫ D.g ∧ D.t' ≫ D.f2' = D.f1' ≫ φ ∧
        ∀ hπ : φ ≫ πO2 = πO1 ≫ D.g, inducedKernelMap πO1 D.g πO2 φ hπ = D.ν := sorry

/-- A fitting map is compatible with the thickenings π_{𝒪ⱼ}. -/
theorem Fits.comm_π (D : RelativeDiagram πO1 πB1 πO2 πB2) {φ : O1' ⟶ O2'}
    (h : Fits D φ) : φ ≫ πO2 = πO1 ≫ D.g := sorry

/-- A fitting map is compatible with the structure maps f'ⱼ. -/
theorem Fits.comm_f' (D : RelativeDiagram πO1 πB1 πO2 πB2) {φ : O1' ⟶ O2'}
    (h : Fits D φ) : D.t' ≫ D.f2' = D.f1' ≫ φ := sorry

/-- A fitting map induces the given g-map of kernel ideals. -/
theorem Fits.induces (D : RelativeDiagram πO1 πB1 πO2 πB2) {φ : O1' ⟶ O2'}
    (h : Fits D φ) (hπ : φ ≫ πO2 = πO1 ≫ D.g) :
    inducedKernelMap πO1 D.g πO2 φ hπ = D.ν := sorry

/-- The front row 0 ⟶ 𝒢₁ ⟶ 𝒪'₁ ⟶ 𝒪₁ ⟶ 0 is short exact. -/
theorem row_front_O_shortExact (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    (KernelIdeal.underlyingShortComplex πO1).ShortExact := sorry

/-- The front base row 0 ⟶ 𝒥₁ ⟶ 𝒪_{B'₁} ⟶ 𝒪_{B₁} ⟶ 0 is short exact. -/
theorem row_front_B_shortExact (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    (KernelIdeal.underlyingShortComplex πB1).ShortExact := sorry

/-- The back row 0 ⟶ 𝒢₂ ⟶ 𝒪'₂ ⟶ 𝒪₂ ⟶ 0 is short exact. -/
theorem row_back_O_shortExact (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    (KernelIdeal.underlyingShortComplex πO2).ShortExact := sorry

/-- The back base row 0 ⟶ 𝒥₂ ⟶ 𝒪_{B'₂} ⟶ 𝒪_{B₂} ⟶ 0 is short exact. -/
theorem row_back_B_shortExact (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    (KernelIdeal.underlyingShortComplex πB2).ShortExact := sorry

end RelativeDiagram

end SheafOfModules.RingedSite.FirstOrderThickening
