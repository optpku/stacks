/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap91.Lemma_91_7_1_Diagram
public import stacks_project.Chap91.Lemma_91_7_1_Obstruction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Obstruction and torsor of fillers of a relative first-order thickening diagram

Given the commutative first-order cube 91.7.1.1 and a g-map of kernel ideals making
91.7.1.2, with front and back solutions of 91.7.0.1, there is a canonical class in
`Ext⁽1⁾(L(g)^* NL[f₁], 𝒢₂)` that vanishes iff a morphism `X'₂ ⟶ X'₁` fits the cube
compatibly with `ν`. When nonempty, those morphisms form a principal homogeneous space
under `Hom(Ω[f₁], g_* 𝒢₂)`.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening

variable {X2 X'2 S2 S'2 X1 X'1 S1 S'1 : RingedSpace.{u}}
variable {i2 : X2 ⟶ X'2} {f2 : X2 ⟶ S2} {f'2 : X'2 ⟶ S'2} {t2 : S2 ⟶ S'2}
variable {i1 : X1 ⟶ X'1} {f1 : X1 ⟶ S1} {f'1 : X'1 ⟶ S'1} {t1 : S1 ⟶ S'1}
variable {g : X2 ⟶ X1} {s : S2 ⟶ S1} {s' : S'2 ⟶ S'1}
variable [IsFirstOrderThickening i2] [IsFirstOrderThickening t2]
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening t1]

/-- Lemma 91.7.1 (1) Given a commutative diagram of morphisms of ringed spaces whose
horizontal arrows are first-order thickenings, and a g-map `ν : 𝒢₁ ⟶ g_* 𝒢₂` making
the left kernel square of 91.7.1.2 commute, with front and back solutions of 91.7.0.1,
the canonical class `mapObstruction D` in `Ext⁽1⁾(L(g)^* NL[f₁], 𝒢₂)` vanishes if and
only if there exists a morphism of ringed spaces `X'₂ ⟶ X'₁` fitting into 91.7.1.1
compatibly with `ν`. -/
@[stacks 08U8]
theorem mapObstruction_eq_zero_iff
    (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    mapObstruction D = 0 ↔ Nonempty (FittingMap D) := sorry

/-- Lemma 91.7.1 (2) If there exists a morphism `X'₂ ⟶ X'₁` fitting into 91.7.1.1
compatibly with `ν`, the set of all such morphisms is a principal homogeneous space
under `Hom_{𝒪_{X₁}}(Ω[f₁], g_* 𝒢₂)`, equivalently `Hom_{𝒪_{X₂}}(g^* Ω[f₁], 𝒢₂)` via
`homOmegaPushforwardEquiv` and `Ext⁽0⁾(L(g)^* NL[f₁], 𝒢₂)` via bijective
`homOmegaExtZero`. -/
@[stacks 08U8]
theorem fittingMap_principalHomogeneous
    (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s')
    (φ φ' : FittingMap D) :
    ∃! α : Ω[f1] ⟶ (g _*).obj (idealModule i2), FittingMap.perturb α φ = φ' := sorry

end AlgebraicGeometry.RingedSpace.Thickening
