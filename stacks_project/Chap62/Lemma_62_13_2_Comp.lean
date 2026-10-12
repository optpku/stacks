/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap62.Lemma_62_5_1_Operations
public import stacks_project.Chap62.Remark_62_5_6_Support_Family

/-!
# Restriction of fibre-cycle families along an open of the total space

This file restricts a family of cycles on the fibres of `X / S` along an open
of `X`, keeping the base scheme `S`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/-- Restriction of a family of cycles on the fibres of `X / S` along an open of
`X`, as a family on the fibres of `U / S`. -/
noncomputable def restrictOver {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℤ} (α : CyclesOnFibers f r) (U : X.Opens) :
    CyclesOnFibers (U.ι ≫ f) r :=
  FiberCycleFamily.reindex (add_zero r)
    (FiberCycleFamily.flatPullback U.ι rfl 0 α)

/-- Coefficients of a total-space restriction are the original fibre
coefficients along the identity-triangle fibre map. -/
theorem restrictOver_apply {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℤ} (α : CyclesOnFibers f r) (U : X.Opens)
    (s : S) (x : (U.ι ≫ f).fiber s) :
    toAlgebraicCycle (restrictOver α U) s x =
      toAlgebraicCycle α s (idTriangleFiberMap U.ι rfl s x) := sorry

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
