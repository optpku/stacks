/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.CommDiagram

/-!
# Relative first-order thickening diagrams of ringed spaces

A relative diagram packages a commutative first-order cube together with a g-map
of kernel ideals making the left square of the compatible kernel diagram commute. A fitting map is a morphism
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
    kernelMapFront h = kernelMapOf t1 f1 i1 inferInstance f'1 h.front.w := rfl

/-- The vertical map `c₂ : 𝒥₂ ⟶ (f₂)_* 𝒢₂` induced by the back face. -/
def kernelMapBack (h : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    idealModule t2 ⟶ (f2 _*).obj (idealModule i2) :=
  kernelMapOf t2 f2 i2 inferInstance f'2 h.back.w

/-- `kernelMapBack` is the kernel comparison of the back face. -/
theorem kernelMapBack_eq (h : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    kernelMapBack h = kernelMapOf t2 f2 i2 inferInstance f'2 h.back.w := rfl

/-- The comparison `𝒥₁ ⟶ s_* 𝒥₂` induced by the bottom face. -/
def kernelMapBase (h : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    idealModule t1 ⟶ (s _*).obj (idealModule t2) :=
  kernelMapOf t1 s t2 inferInstance s' h.bottom.w

/-- `kernelMapBase` is the kernel comparison of the bottom face. -/
theorem kernelMapBase_eq (h : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    kernelMapBase h = kernelMapOf t1 s t2 inferInstance s' h.bottom.w := rfl

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
          (pushforwardCompIso g f1).hom.app (idealModule i2) := rfl

/-- The left kernel compatibility equation: `c₁` then `ν` equals the kernel map of `s'` then `c₂`,
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
        kernelMapBase h ≫ (s _*).map (kernelMapBack h) ≫ pushforwardLeftIso h := Iff.rfl

/-- A commutative first-order cube together with a `g`-map of kernel ideals making the left
square of the compatible kernel diagram commute. The morphism `X'₂ ⟶ X'₁` is not part of the data. -/
structure RelativeDiagram
    (i2 : X2 ⟶ X'2) (f2 : X2 ⟶ S2) (f'2 : X'2 ⟶ S'2) (t2 : S2 ⟶ S'2)
    (i1 : X1 ⟶ X'1) (f1 : X1 ⟶ S1) (f'1 : X'1 ⟶ S'1) (t1 : S1 ⟶ S'1)
    (g : X2 ⟶ X1) (s : S2 ⟶ S1) (s' : S'2 ⟶ S'1)
    [IsFirstOrderThickening i2] [IsFirstOrderThickening t2]
    [IsFirstOrderThickening i1] [IsFirstOrderThickening t1] where
  /-- The four commuting faces of the underlying diagram. -/
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

/-- The present faces of a relative diagram are the four commutative squares of the four-face diagram. -/
theorem spec (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    CommSq i2 f2 f'2 t2 ∧ CommSq i1 f1 f'1 t1 ∧
      CommSq f2 g s f1 ∧ CommSq t2 s s' t1 := ⟨D.comm.back, D.comm.front, D.comm.left, D.comm.bottom⟩

/-- The left kernel square of a relative diagram commutes. -/
theorem spec_kernel :
    kernelMapFront D.comm ≫ (f1 _*).map D.ν =
      kernelMapBase D.comm ≫ (s _*).map (kernelMapBack D.comm) ≫
        pushforwardLeftIso D.comm := D.comm_kernel

/-- The front solution square. -/
theorem frontSq (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') : CommSq i1 f1 f'1 t1 := D.comm.front

/-- The back solution square. -/
theorem backSq (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') : CommSq i2 f2 f'2 t2 := D.comm.back

/-- The vertical map `c₁ : 𝒥₁ ⟶ (f₁)_* 𝒢₁` of the relative diagram. -/
def c : idealModule t1 ⟶ (f1 _*).obj (idealModule i1) :=
  kernelMapFront D.comm

/-- `c` is the front kernel comparison of the underlying cube. -/
theorem c_eq : c D = kernelMapFront D.comm := rfl

/-- The vertical map `c₂ : 𝒥₂ ⟶ (f₂)_* 𝒢₂` of the relative diagram. -/
def c_back : idealModule t2 ⟶ (f2 _*).obj (idealModule i2) :=
  kernelMapBack D.comm

/-- `c_back` is the back kernel comparison of the underlying cube. -/
theorem c_back_eq : c_back D = kernelMapBack D.comm := rfl

/-- The front face of a relative diagram, as a solution of the deformation square with kernel identification
the identity on `Ker(i₁^♯)`. -/
def frontSolution :
    Solution t1 f1 (idealModule i1) (kernelMapFront D.comm) :=
  Solution.of t1 f1 (idealModule i1) (kernelMapFront D.comm)
    i1 f'1 D.comm.front.w (Iso.refl _) (by simp [kernelMapFront])

/-- `frontSolution` is the front first-order thickening with identity kernel identification. -/
theorem frontSolution_spec :
    (frontSolution D).i = i1 ∧ (frontSolution D).f' = f'1 ∧
      (frontSolution D).kernelIso = Iso.refl _ := ⟨rfl, rfl, rfl⟩

/-- The back face of a relative diagram, as a solution of the deformation square with kernel identification
the identity on `Ker(i₂^♯)`. -/
def backSolution :
    Solution t2 f2 (idealModule i2) (kernelMapBack D.comm) :=
  Solution.of t2 f2 (idealModule i2) (kernelMapBack D.comm)
    i2 f'2 D.comm.back.w (Iso.refl _) (by simp [kernelMapBack])

/-- `backSolution` is the back first-order thickening with identity kernel identification. -/
theorem backSolution_spec :
    (backSolution D).i = i2 ∧ (backSolution D).f' = f'2 ∧
      (backSolution D).kernelIso = Iso.refl _ := ⟨rfl, rfl, rfl⟩

/-- The four commuting faces identify the two composites from the back space to the front base. -/
theorem g_comp_i1_f'1_eq (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    g ≫ i1 ≫ f'1 = i2 ≫ f'2 ≫ s' := by
  rw [D.comm.front.w, ← Category.assoc, ← D.comm.left.w, Category.assoc,
    ← D.comm.bottom.w, ← Category.assoc, ← D.comm.back.w, Category.assoc]

end RelativeDiagram

end AlgebraicGeometry.RingedSpace.Thickening
