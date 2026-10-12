/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap77.Situation_77_12_1_FormalSystem

/-!
# Finite-stage fibre products of étale opens

In Situation 77.12.1, an open `U ⟶ X` has finite-stage fibre products
`U_n = U ×_X X_n`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem

/-- The finite-stage fibre product `U_n = U ×_X X_n`. -/
def stagePullback (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ) :
    AlgebraicSpace (Spec S.limitCone.cone.pt) :=
  Limits.pullback f (S.stageToSpace n)

/-- `stagePullback S f n` is the categorical fibre product of `f` and `stageToSpace n`. -/
theorem stagePullback_eq (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ) :
    stagePullback S f n = Limits.pullback f (S.stageToSpace n) :=
  sorry

/-- The projection `U_n ⟶ U` of the finite-stage fibre product. -/
abbrev stagePullback_fst (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ) :
    stagePullback S f n ⟶ U :=
  Limits.pullback.fst f (S.stageToSpace n)

/-- `stagePullback_fst` is the first projection of `U ×_X X_n`. -/
theorem stagePullback_fst_eq (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ) :
    stagePullback_fst S f n = Limits.pullback.fst f (S.stageToSpace n) :=
  sorry

/-- The projection `U_n ⟶ X_n` of the finite-stage fibre product. -/
abbrev stagePullback_snd (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ) :
    stagePullback S f n ⟶ S.stageSpace n :=
  Limits.pullback.snd f (S.stageToSpace n)

/-- `stagePullback_snd` is the second projection of `U ×_X X_n`. -/
theorem stagePullback_snd_eq (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ) :
    stagePullback_snd S f n = Limits.pullback.snd f (S.stageToSpace n) :=
  sorry

/-- The projections exhibit `U_n` as the fibre product `U ×_X X_n`. -/
theorem stagePullback_isPullback (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ) :
    IsPullback (stagePullback_fst S f n) (stagePullback_snd S f n) f (S.stageToSpace n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
