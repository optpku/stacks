/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Definition_59_95_1
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.SetTheory.Cardinal.ENat
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K]
variable [HasSheafify (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u})]
variable {L : Type u} [Field L] [Algebra K L]
variable [HasSheafify (Spec (CommRingCat.of L)).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Spec (CommRingCat.of L)).smallEtaleTopology AddCommGrpCat.{u})]

/-- Lemma 59.95.4: if `L / K` is a field extension, then
`cohomologicalDimension (Spec (CommRingCat.of L)) ≤
  cohomologicalDimension (Spec (CommRingCat.of K)) +
    Cardinal.toENat (Algebra.trdeg K L)`. Infinite transcendence degree is read as `⊤`. -/
@[stacks 0F0T]
theorem cohomologicalDimension_le_add_trdeg :
    cohomologicalDimension (Spec (CommRingCat.of L)) ≤
      cohomologicalDimension (Spec (CommRingCat.of K)) +
        @id (WithTop ℕ) (Cardinal.toENat (Algebra.trdeg K L)) := sorry

/-- Vanishing bound form of the field-extension comparison for cohomological dimension. -/
theorem cohomologicalDimensionBound_add_trdeg :
    cohomologicalDimensionBound (Spec (CommRingCat.of L))
      (cohomologicalDimension (Spec (CommRingCat.of K)) +
        @id (WithTop ℕ) (Cardinal.toENat (Algebra.trdeg K L))) := sorry

end AlgebraicGeometry.Scheme

end
