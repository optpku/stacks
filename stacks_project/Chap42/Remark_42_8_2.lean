/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Remark_42_8_2_Pointwise
public import stacks_project.Chap42.Situation_42_7_1
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.CycleGroup

universe u

variable {S X : Scheme.{u}} (f : X ⟶ S)
variable [UniversallyCatenary S] [LocallyOfFiniteType f]
variable (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)

/-- Remark 42.8.2: under Situation 42.7.1, if `X` is locally of finite type over `S` and
`k : ℤ`, then `CycleGroup X (f.relativeDimensionFunction δ) k` is the primed/locally
finite subgroup of the product of `MilnorK.Group 0 (X.residueField x)` over points `x`
with `f.relativeDimensionFunction δ x = k`, included in the unrestricted product. -/
@[stacks 0GU2]
noncomputable def AlgebraicGeometry.CycleGroup.pointwiseEquiv :
    CycleGroup X (f.relativeDimensionFunction δ) k ≃+
      Pointwise.locallyFinite (f.relativeDimensionFunction δ) k :=
  Pointwise.equiv (f.relativeDimensionFunction δ) k

/-- Evaluating the identification of `Z_k(X)` with the primed `K₀ᴹ` product is pointwise
`degreeZeroMap`. -/
theorem AlgebraicGeometry.CycleGroup.pointwiseEquiv_apply
    (α : CycleGroup X (f.relativeDimensionFunction δ) k)
    (x : {x : X // f.relativeDimensionFunction δ x = k}) :
    (pointwiseEquiv f δ k α).1 x =
      MilnorK.degreeZeroMap (X.residueField x.1)
        (toAlgebraicCycle (f.relativeDimensionFunction δ) k α x.1) := sorry

#check (Pointwise.locallyFinite (f.relativeDimensionFunction δ) k).subtype
#check MilnorK.degreeZeroMap_bijective
