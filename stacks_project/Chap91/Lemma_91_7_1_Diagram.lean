/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap91.«91_7_0_1_Solution»
public import stacks_project.Chap91.«91_7_1_1_Diagram»

/-!
# Relative first-order thickening diagrams of ringed spaces

A relative diagram packages the commutative first-order cube 91.7.1.1 together with a g-map
of kernel ideals making the left square of 91.7.1.2 commute. A fitting map is a morphism
`X'₂ ⟶ X'₁` filling the omitted edge compatibly with that g-map.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening

variable {X2 X'2 S2 S'2 X1 X'1 S1 S'1 : RingedSpace.{u}}
variable {i2 : X2 ⟶ X'2} {f2 : X2 ⟶ S2} {f'2 : X'2 ⟶ S'2} {t2 : S2 ⟶ S'2}
variable {i1 : X1 ⟶ X'1} {f1 : X1 ⟶ S1} {f'1 : X'1 ⟶ S'1} {t1 : S1 ⟶ S'1}
variable {g : X2 ⟶ X1} {s : S2 ⟶ S1} {s' : S'2 ⟶ S'1}
variable [IsFirstOrderThickening i2] [IsFirstOrderThickening t2]
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening t1]

/-- The vertical map `c₁ : 𝒥₁ ⟶ (f₁)_* 𝒢₁` induced by the front face. -/
def kernelMapFront (h : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    idealModule t1 ⟶ (f1 _*).obj (idealModule i1) :=
  kernelMapOf t1 f1 i1 inferInstance f'1 h.front.w

/-- `kernelMapFront` is the kernel comparison of the front face. -/
theorem kernelMapFront_eq (h : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    kernelMapFront h = kernelMapOf t1 f1 i1 inferInstance f'1 h.front.w := sorry

/-- The vertical map `c₂ : 𝒥₂ ⟶ (f₂)_* 𝒢₂` induced by the back face. -/
def kernelMapBack (h : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    idealModule t2 ⟶ (f2 _*).obj (idealModule i2) :=
  kernelMapOf t2 f2 i2 inferInstance f'2 h.back.w

/-- `kernelMapBack` is the kernel comparison of the back face. -/
theorem kernelMapBack_eq (h : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    kernelMapBack h = kernelMapOf t2 f2 i2 inferInstance f'2 h.back.w := sorry

/-- The comparison `𝒥₁ ⟶ s_* 𝒥₂` induced by the bottom face. -/
def kernelMapBase (h : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    idealModule t1 ⟶ (s _*).obj (idealModule t2) :=
  kernelMapOf t1 s t2 inferInstance s' h.bottom.w

/-- `kernelMapBase` is the kernel comparison of the bottom face. -/
theorem kernelMapBase_eq (h : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    kernelMapBase h = kernelMapOf t1 s t2 inferInstance s' h.bottom.w := sorry

/-- Reassociation of `s_* (f₂)_*` with `(f₁)_* g_*` along the left face `f₂ ≫ s = g ≫ f₁`. -/
def pushforwardLeftIso (h : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    (s _*).obj ((f2 _*).obj (idealModule i2)) ⟶
      (f1 _*).obj ((g _*).obj (idealModule i2)) :=
  (pushforwardCompIso f2 s).inv.app (idealModule i2) ≫
    (eqToIso (congrArg pushforward h.left.w)).hom.app (idealModule i2) ≫
      (pushforwardCompIso g f1).hom.app (idealModule i2)

/-- `pushforwardLeftIso` is the composite of the two pushforward composition isomorphisms
and the left-face equality. -/
theorem pushforwardLeftIso_eq (h : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    pushforwardLeftIso h =
      (pushforwardCompIso f2 s).inv.app (idealModule i2) ≫
        (eqToIso (congrArg pushforward h.left.w)).hom.app (idealModule i2) ≫
          (pushforwardCompIso g f1).hom.app (idealModule i2) := sorry

/-- The left kernel square of 91.7.1.2: `c₁` then `ν` equals the kernel map of `s'` then `c₂`,
as maps of `𝒪_{S₁}`-modules. -/
def KernelSquare (h : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s')
    (ν : idealModule i1 ⟶ (g _*).obj (idealModule i2)) : Prop :=
  kernelMapFront h ≫ (f1 _*).map ν =
    kernelMapBase h ≫ (s _*).map (kernelMapBack h) ≫ pushforwardLeftIso h

/-- The left kernel square commutes iff `c₁` then `ν` equals the base kernel map then `c₂`. -/
theorem KernelSquare_iff (h : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s')
    (ν : idealModule i1 ⟶ (g _*).obj (idealModule i2)) :
    KernelSquare h ν ↔
      kernelMapFront h ≫ (f1 _*).map ν =
        kernelMapBase h ≫ (s _*).map (kernelMapBack h) ≫ pushforwardLeftIso h := sorry

/-- A commutative first-order cube together with a `g`-map of kernel ideals making the left
square of 91.7.1.2 commute. The morphism `X'₂ ⟶ X'₁` is not part of the data. -/
structure RelativeDiagram
    (i2 : X2 ⟶ X'2) (f2 : X2 ⟶ S2) (f'2 : X'2 ⟶ S'2) (t2 : S2 ⟶ S'2)
    (i1 : X1 ⟶ X'1) (f1 : X1 ⟶ S1) (f'1 : X'1 ⟶ S'1) (t1 : S1 ⟶ S'1)
    (g : X2 ⟶ X1) (s : S2 ⟶ S1) (s' : S'2 ⟶ S'1)
    [IsFirstOrderThickening i2] [IsFirstOrderThickening t2]
    [IsFirstOrderThickening i1] [IsFirstOrderThickening t1] where
  /-- The underlying commutative diagram 91.7.1.1. -/
  comm : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s'
  /-- The given `g`-map `ν : 𝒢₁ ⟶ g_* 𝒢₂` of kernel ideals. -/
  ν : idealModule i1 ⟶ (g _*).obj (idealModule i2)
  /-- The left kernel square commutes. -/
  comm_kernel : KernelSquare comm ν

namespace RelativeDiagram

/-- Assemble a relative diagram from a commutative cube, a `g`-map of kernel ideals, and
commutativity of the left kernel square. -/
def of (comm : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s')
    (ν : idealModule i1 ⟶ (g _*).obj (idealModule i2))
    (comm_kernel : KernelSquare comm ν) :
    RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s' where
  comm := comm
  ν := ν
  comm_kernel := comm_kernel

variable (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s')

/-- The present faces of a relative diagram are the four commutative squares of 91.7.1.1. -/
theorem spec :
    CommSq i2 f2 f'2 t2 ∧ CommSq i1 f1 f'1 t1 ∧
      CommSq f2 g s f1 ∧ CommSq t2 s s' t1 := sorry

/-- The left kernel square of a relative diagram commutes. -/
theorem spec_kernel :
    kernelMapFront D.comm ≫ (f1 _*).map D.ν =
      kernelMapBase D.comm ≫ (s _*).map (kernelMapBack D.comm) ≫
        pushforwardLeftIso D.comm := sorry

/-- The front solution square. -/
theorem frontSq : CommSq i1 f1 f'1 t1 := sorry

/-- The back solution square. -/
theorem backSq : CommSq i2 f2 f'2 t2 := sorry

/-- The vertical map `c₁ : 𝒥₁ ⟶ (f₁)_* 𝒢₁` of the relative diagram. -/
def c : idealModule t1 ⟶ (f1 _*).obj (idealModule i1) :=
  kernelMapFront D.comm

/-- `c` is the front kernel comparison of the underlying cube. -/
theorem c_eq : c D = kernelMapFront D.comm := sorry

/-- The vertical map `c₂ : 𝒥₂ ⟶ (f₂)_* 𝒢₂` of the relative diagram. -/
def c_back : idealModule t2 ⟶ (f2 _*).obj (idealModule i2) :=
  kernelMapBack D.comm

/-- `c_back` is the back kernel comparison of the underlying cube. -/
theorem c_back_eq : c_back D = kernelMapBack D.comm := sorry

/-- The front face of a relative diagram, as a solution of 91.7.0.1 with kernel identification
the identity on `Ker(i₁^♯)`. -/
def frontSolution :
    Solution t1 f1 (idealModule i1) (kernelMapFront D.comm) :=
  Solution.of t1 f1 (idealModule i1) (kernelMapFront D.comm)
    i1 f'1 D.comm.front.w (Iso.refl _) sorry

/-- `frontSolution` is the front first-order thickening with identity kernel identification. -/
theorem frontSolution_spec :
    (frontSolution D).i = i1 ∧ (frontSolution D).f' = f'1 ∧
      (frontSolution D).kernelIso = Iso.refl _ := sorry

/-- The back face of a relative diagram, as a solution of 91.7.0.1 with kernel identification
the identity on `Ker(i₂^♯)`. -/
def backSolution :
    Solution t2 f2 (idealModule i2) (kernelMapBack D.comm) :=
  Solution.of t2 f2 (idealModule i2) (kernelMapBack D.comm)
    i2 f'2 D.comm.back.w (Iso.refl _) sorry

/-- `backSolution` is the back first-order thickening with identity kernel identification. -/
theorem backSolution_spec :
    (backSolution D).i = i2 ∧ (backSolution D).f' = f'2 ∧
      (backSolution D).kernelIso = Iso.refl _ := sorry

end RelativeDiagram

/-- A morphism `X'₂ ⟶ X'₁` fitting into 91.7.1.1 compatibly with the given `g`-map `ν`. -/
structure FittingMap (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') where
  /-- The filling morphism of ringed spaces `X'₂ ⟶ X'₁`. -/
  hom : X'2 ⟶ X'1
  /-- The top square with `i₂`, `g`, and `i₁` commutes. -/
  comm_top : i2 ≫ hom = g ≫ i1
  /-- The right square with `f'₁`, `f'₂`, and `s'` commutes. -/
  comm_right : hom ≫ f'1 = f'2 ≫ s'
  /-- The filling morphism induces the given `g`-map on kernel ideals. -/
  induces : kernelMapOf i1 g i2 inferInstance hom comm_top = D.ν

namespace FittingMap

variable {D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s'}

/-- Assemble a fitting map from a morphism `X'₂ ⟶ X'₁` and the three compatibility conditions. -/
def of (hom : X'2 ⟶ X'1) (comm_top : i2 ≫ hom = g ≫ i1)
    (comm_right : hom ≫ f'1 = f'2 ≫ s')
    (induces : kernelMapOf i1 g i2 inferInstance hom comm_top = D.ν) :
    FittingMap D where
  hom := hom
  comm_top := comm_top
  comm_right := comm_right
  induces := induces

/-- A fitting map makes the top and right faces commute and induces `ν` on kernels. -/
theorem spec (φ : FittingMap D) :
    i2 ≫ φ.hom = g ≫ i1 ∧ φ.hom ≫ f'1 = f'2 ≫ s' ∧
      kernelMapOf i1 g i2 inferInstance φ.hom φ.comm_top = D.ν := sorry

/-- A morphism `X'₂ ⟶ X'₁` underlies a fitting map if and only if the two present faces
through it commute and it induces `ν` on kernel ideals. -/
theorem fits_iff (hom : X'2 ⟶ X'1) :
    (∃ φ : FittingMap D, φ.hom = hom) ↔
      ∃ (comm_top : i2 ≫ hom = g ≫ i1),
        hom ≫ f'1 = f'2 ≫ s' ∧
          kernelMapOf i1 g i2 inferInstance hom comm_top = D.ν := sorry

end FittingMap

end AlgebraicGeometry.RingedSpace.Thickening
