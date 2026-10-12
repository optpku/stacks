/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.SerreQuotient
public import stacks_project.Chap103.Lemma_103_10_2

/-!
# Remark 103.10.7

On an algebraic stack, `QCoh` is the Serre quotient of `LQCoh^{fbc}` by parasitic
objects, and the inclusion `QCoh.toLQCohFbc` is left adjoint to that quotient.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Parasitic objects of `LQCohFbc X` form a Serre class. -/
instance LQCohFbc.parasitic_isSerreClass (X : GroupoidsOver S) [AlgebraicStack X] :
    IsSerreClass (LQCohFbc.parasitic X) :=
  sorry

/-- Remark 103.10.7: for an algebraic stack `X`, the category `QCoh X` of
quasi-coherent modules is the Serre quotient of `LQCohFbc X` by parasitic
objects. Equivalently, `LQCohFbc.toQCoh X` is a localization of `LQCohFbc X`
at `(LQCohFbc.parasitic X).isoModSerre`. This is Homology, Lemma 12.10.6 applied
to Lemmas 103.10.1 and 103.10.2: `toQCoh` is exact with kernel
`LQCohFbc.parasitic X`. The inclusion `QCoh.toLQCohFbc X` is left adjoint to
this quotient functor. A similar result on derived categories is Lemma 104.5.4. -/
@[stacks 07B2]
instance LQCohFbc.toQCoh_isLocalization (X : GroupoidsOver S) [AlgebraicStack X] :
    (LQCohFbc.toQCoh X).IsLocalization (LQCohFbc.parasitic X).isoModSerre :=
  sorry

end AlgebraicGeometry.GroupoidsOver
