/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap82.Definition_82_26_2_ChowCohomology
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap68.Definition_68_25_4_UniversallyCatenary
public import stacks_project.Chap71.Definition_71_7_6_ZeroScheme
public import stacks_project.Chap76.Lemma_76_32_2
public import stacks_project.Chap82.Definition_82_3_1_CycleGroup

/-!
# Scheme-theoretic intersection cycles for refined Gysin maps

The multiplicity-weighted associated cycle of `Z(s) ∩ closure({x})` on the
zero scheme, as a locally finite function on `|Z(s)|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open Function

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (k : ℤ)
variable (L : X.Modules) [isInvertibleObject L] (s : L.sections)
variable [QuasiSeparated (zeroSchemeι L s ≫ f)]
variable [LocallyOfFiniteType (zeroSchemeι L s ≫ f)]

/-- The multiplicity-weighted `k`-cycle of the scheme-theoretic intersection of
`Z(s)` with the reduced closure of `x`, as a locally finite function on
`|Z(s)|`. Coefficients are lengths of `𝒪` at generic points of dimension `k`,
so a section such as `t^2` on `𝔸¹` contributes coefficient `2`. -/
noncomputable def gysinIntersectionCycle (x : Points X) :
    Function.locallyFinsupp (Points (zeroScheme L s).X) ℤ :=
  @ClosedSubspace.associatedCycle S (zeroScheme L s).X
    (LocallyOfFiniteType.isLocallyNoetherian (zeroSchemeι L s ≫ f))
    ((ClosedSubspace.pointClosure x).inverseImage (zeroSchemeι L s))
    (Hom.relativeDimensionFunction (zeroSchemeι L s ≫ f) δ) k

/-- The intersection cycle of `Z(s) ∩ closure({x})` is a degree-`k` cycle on
`Z(s)`. -/
theorem gysinIntersectionCycle_mem (x : Points X) :
    gysinIntersectionCycle f δ k L s x ∈
      Hom.cycleGroup (zeroSchemeι L s ≫ f) δ k :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
