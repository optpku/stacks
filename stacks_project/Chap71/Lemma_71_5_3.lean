/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap71.Lemma_71_5_3_FittingIdeal

/-!
# Lemma 71.5.3

The scheme-theoretic support of a finite-type quasi-coherent module on an
algebraic space is contained in the closed subspace cut out by the zeroth
Fitting ideal, both have underlying set the ordinary support, and the module
descends to a finite-type quasi-coherent module on that Fitting closed
subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]

/-- Lemma 71.5.3 (1): the scheme-theoretic support of `F` factors through the
closed subspace cut out by `Fit_0(F)`, as closed subspaces of `X`. -/
@[stacks 0CZ6]
theorem schemeTheoreticSupport_le_fittingIdealZeroSubspace
    {Z : AlgebraicSpace S} (i : Z ⟶ X) [IsSchemeTheoreticSupport F i] :
    ∃ f : Z ⟶ (fittingIdealZeroSubspace F).X,
      f ≫ (fittingIdealZeroSubspace F).ι = i :=
  sorry

/-- Lemma 71.5.3 (2): the scheme-theoretic support and the closed subspace cut
out by `Fit_0(F)` have the same underlying point-set, equal to the support of
`F` in `|X|`. -/
@[stacks 0CZ6]
theorem fittingIdealZeroSubspace_pointsSet_eq_moduleSupport
    {Z : AlgebraicSpace S} (i : Z ⟶ X) [IsSchemeTheoreticSupport F i] :
    Set.range (Points.map i) = (fittingIdealZeroSubspace F).pointsSet ∧
      (fittingIdealZeroSubspace F).pointsSet = moduleSupport F :=
  sorry

/-- Lemma 71.5.3 (3): `F` is the pushforward of a finite-type quasi-coherent
module on the closed subspace cut out by `Fit_0(F)`. -/
@[stacks 0CZ6]
theorem exists_finiteType_module_pushforward_fittingIdealZero :
    ∃ G0 : (fittingIdealZeroSubspace F).X.Modules,
      G0.IsQuasicoherent ∧ G0.IsFiniteType ∧
        Nonempty ((pushforward (fittingIdealZeroSubspace F).ι).obj G0 ≅ F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
