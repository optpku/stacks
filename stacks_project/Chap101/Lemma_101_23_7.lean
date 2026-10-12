/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap101.Lemma_101_23_7_Covering

/-!
# Covering characterizations of locally quasi-finite morphisms of algebraic stacks

A morphism of algebraic stacks is locally quasi-finite if and only if it is
quasi-DM and locally quasi-finite algebraic-space maps into 2-fibre products
remain locally quasi-finite after composing to the test space, if and only if
every algebraic-space test of the target has such a cover of the 2-fibre
product, and if and only if some fppf algebraic-space cover of the target has
such a cover of the 2-fibre product.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)

/-- Lemma 101.23.7: for a morphism `f : X ⟶ Y` of algebraic stacks, the
following are equivalent: `LocallyQuasiFinite f`; `QuasiDM f` and
`forallSpaceMaps f`; `existsCoverOnPullbacks f`; and `existsCoverOverFppf f`. -/
@[stacks 06UF]
theorem tfae :
    List.TFAE [LocallyQuasiFinite f, QuasiDM f ∧ forallSpaceMaps f,
      existsCoverOnPullbacks f, existsCoverOverFppf f] :=
  sorry

/-- A morphism of algebraic stacks is locally quasi-finite iff it is quasi-DM
and locally quasi-finite algebraic-space maps into 2-fibre products remain
locally quasi-finite after composing to the test space. -/
theorem iff_forallSpaceMaps :
    LocallyQuasiFinite f ↔ QuasiDM f ∧ forallSpaceMaps f :=
  sorry

/-- A morphism of algebraic stacks is locally quasi-finite iff every
algebraic-space test of the target has a locally quasi-finite flat
algebraic-space cover of the 2-fibre product whose composite to the test
space is locally quasi-finite. -/
theorem iff_existsCoverOnPullbacks :
    LocallyQuasiFinite f ↔ existsCoverOnPullbacks f :=
  sorry

/-- A morphism of algebraic stacks is locally quasi-finite iff some fppf
algebraic-space cover of the target has a locally quasi-finite flat
algebraic-space cover of the 2-fibre product whose composite to that cover
is locally quasi-finite. -/
theorem iff_existsCoverOverFppf :
    LocallyQuasiFinite f ↔ existsCoverOverFppf f :=
  sorry

/-- A locally quasi-finite morphism of algebraic stacks preserves locally
quasi-finite algebraic-space maps into 2-fibre products after composing to
the test space. -/
theorem forallSpaceMaps_of [LocallyQuasiFinite f] : forallSpaceMaps f :=
  sorry

/-- Quasi-DM together with preservation of locally quasi-finite algebraic-space
maps into 2-fibre products implies that a morphism of algebraic stacks is
locally quasi-finite. -/
theorem of_forallSpaceMaps [QuasiDM f] (h : forallSpaceMaps f) :
    LocallyQuasiFinite f :=
  sorry

/-- A locally quasi-finite morphism of algebraic stacks admits a locally
quasi-finite flat algebraic-space cover of every 2-fibre product against an
algebraic space over the target, with locally quasi-finite composite to that
space. -/
theorem existsCoverOnPullbacks_of [LocallyQuasiFinite f] :
    existsCoverOnPullbacks f :=
  sorry

/-- The covering criterion on every algebraic-space test of the target implies
that a morphism of algebraic stacks is locally quasi-finite. -/
theorem of_existsCoverOnPullbacks (h : existsCoverOnPullbacks f) :
    LocallyQuasiFinite f :=
  sorry

/-- A locally quasi-finite morphism of algebraic stacks admits some fppf
algebraic-space cover of the target whose 2-fibre product has a locally
quasi-finite flat algebraic-space cover with locally quasi-finite composite
to that cover. -/
theorem existsCoverOverFppf_of [LocallyQuasiFinite f] :
    existsCoverOverFppf f :=
  sorry

/-- An fppf algebraic-space cover of the target together with a locally
quasi-finite flat algebraic-space cover of the 2-fibre product whose
composite to that cover is locally quasi-finite implies that a morphism of
algebraic stacks is locally quasi-finite. -/
theorem of_existsCoverOverFppf (h : existsCoverOverFppf f) :
    LocallyQuasiFinite f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite
