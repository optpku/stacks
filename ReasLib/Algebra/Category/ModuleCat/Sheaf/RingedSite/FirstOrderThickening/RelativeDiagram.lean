/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.KernelMap

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A diagram of first-order thickenings of sheaves of commutative rings on a site, with
front and back solutions and a given g-map of kernel ideals. The morphism 𝒪'₁ ⟶ 𝒪'₂ is
not part of the data. -/
structure RelativeDiagram
    {O1 O1' OB1 OB1' O2 O2' OB2 OB2' : Sheaf J CommRingCat.{w}}
    (πO1 : O1' ⟶ O1) (πB1 : OB1' ⟶ OB1) (πO2 : O2' ⟶ O2) (πB2 : OB2' ⟶ OB2)
    [hπO1 : IsFirstOrderThickening πO1] [hπB1 : IsFirstOrderThickening πB1]
    [hπO2 : IsFirstOrderThickening πO2] [hπB2 : IsFirstOrderThickening πB2] where
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

variable {O1 O1' OB1 OB1' O2 O2' OB2 OB2' : Sheaf J CommRingCat.{w}}
variable {πO1 : O1' ⟶ O1} {πB1 : OB1' ⟶ OB1}
variable {πO2 : O2' ⟶ O2} {πB2 : OB2' ⟶ OB2}
variable [hπO1 : IsFirstOrderThickening πO1] [hπB1 : IsFirstOrderThickening πB1]
variable [hπO2 : IsFirstOrderThickening πO2] [hπB2 : IsFirstOrderThickening πB2]

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
      D.t' ≫ πB2 = πB1 ≫ D.t ∧ D.t ≫ D.f2 = D.f1 ≫ D.g :=
  ⟨D.comm_front, D.comm_back, D.comm_B, D.comm_O⟩

/-- The left kernel square of a relative diagram commutes. -/
theorem spec_kernel (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    toAdditive D.f1 (inducedKernelMap πB1 D.f1 πO1 D.f1' D.comm_front) ≫
        toAdditive D.g D.ν =
      toAdditive D.t (inducedKernelMap πB1 D.t πB2 D.t' D.comm_B) ≫
        toAdditive D.f2 (inducedKernelMap πB2 D.f2 πO2 D.f2' D.comm_back) :=
  D.comm_kernel

/-- The front solution square. -/
theorem frontSq (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    CommSq D.f1' πB1 πO1 D.f1 := ⟨D.comm_front⟩

/-- The back solution square. -/
theorem backSq (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    CommSq D.f2' πB2 πO2 D.f2 := ⟨D.comm_back⟩

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
      inducedKernelAdditiveMap πB1 D.f1 πO1 D.f1' D.comm_front := by
  ext U x
  rfl

/-- Forgetting `c_back` to additive sheaves recovers the additive kernel map of f'₂. -/
theorem c_back_toAdditive (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    toAdditive D.f2 (c_back D) =
      inducedKernelAdditiveMap πB2 D.f2 πO2 D.f2' D.comm_back := by
  ext U x
  rfl

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
        ∀ hπ : φ ≫ πO2 = πO1 ≫ D.g, inducedKernelMap πO1 D.g πO2 φ hπ = D.ν := Iff.rfl

/-- A fitting map is compatible with the thickenings π_{𝒪ⱼ}. -/
theorem Fits.comm_π (D : RelativeDiagram πO1 πB1 πO2 πB2) {φ : O1' ⟶ O2'}
    (h : Fits D φ) : φ ≫ πO2 = πO1 ≫ D.g := h.1

/-- A fitting map is compatible with the structure maps f'ⱼ. -/
theorem Fits.comm_f' (D : RelativeDiagram πO1 πB1 πO2 πB2) {φ : O1' ⟶ O2'}
    (h : Fits D φ) : D.t' ≫ D.f2' = D.f1' ≫ φ := h.2.1

/-- A fitting map induces the given g-map of kernel ideals. -/
theorem Fits.induces (D : RelativeDiagram πO1 πB1 πO2 πB2) {φ : O1' ⟶ O2'}
    (h : Fits D φ) (hπ : φ ≫ πO2 = πO1 ≫ D.g) :
    inducedKernelMap πO1 D.g πO2 φ hπ = D.ν := h.2.2 hπ

end RelativeDiagram

end SheafOfModules.RingedSite.FirstOrderThickening
