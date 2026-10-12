/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap67.Lemma_67_49_1_FiniteComponents
public import stacks_project.Chap71.Lemma_71_6_11_WeaklyAssociated
public import stacks_project.Chap71.Lemma_71_10_4_Stalk

/-!
# Lemma 71.10.4

If every weakly associated point of an algebraic space `X` has codimension `0` and `X`
satisfies Morphisms of Spaces Lemma 67.49.1, then `𝒦_X` is a quasi-coherent sheaf of
`𝒪_X`-algebras, affine étale sections of `𝒦_X` are the total ring of fractions of the
corresponding sections of `𝒪_X`, and at a geometric point the stalk of `𝒮_X` (resp. `𝒦_X`)
is the set of nonzerodivisors (resp. the total ring of fractions) of `𝒪_{X, x̄}`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.10.4 (1): if every weakly associated point of the algebraic space `X` has
codimension `0` and `X` satisfies Morphisms of Spaces Lemma 67.49.1, then `𝒦_X` is a
quasi-coherent sheaf of `𝒪_X`-algebras. -/
@[stacks 0EN6]
theorem meromorphicFunctionSheaf_isQuasicoherent {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X) :
    ((restrictionAlong (toMeromorphicFunctionSheafHom X)).obj
        (unitModule (smallEtaleTopology X) (meromorphicFunctionSheaf X))).IsQuasicoherent :=
  sorry

/-- Lemma 71.10.4 (2): under the same hypotheses, if `U` is affine and étale over `X`, then
`𝒦_X(U)` is the total ring of fractions of `𝒪_X(U)`. -/
@[stacks 0EN6]
theorem meromorphicFunctionSheaf_isLocalization_of_isAffine {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X) (U : affineEtaleSite X) :
    IsLocalization (nonZeroDivisors ((commStructureSheafLift X).obj.obj (op U.obj)))
      ((meromorphicFunctionSheaf X).obj.obj (op U.obj)) :=
  sorry

/-- Lemma 71.10.4 (3): under the same hypotheses, at a geometric point `x̄` the stalk
`𝒮_{x̄}` is the set of nonzerodivisors of `𝒪_{X, x̄}`. -/
@[stacks 0EN6]
theorem meromorphicDenominatorStalk_eq_nonZeroDivisors {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X) (xbar : GeometricPoint X) :
    meromorphicDenominatorStalk xbar = nonZeroDivisors (structureSheafLiftStalk xbar) :=
  sorry

/-- Lemma 71.10.4 (4): under the same hypotheses, at a geometric point `x̄` the stalk
`𝒦_{X, x̄}` is the total ring of fractions of `𝒪_{X, x̄}`. -/
@[stacks 0EN6]
theorem meromorphicFunctionStalk_isLocalization {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X) (xbar : GeometricPoint X) :
    IsLocalization (nonZeroDivisors (structureSheafLiftStalk xbar))
      (meromorphicFunctionStalk xbar) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
