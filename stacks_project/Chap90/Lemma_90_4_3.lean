/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Lemma_90_4_3_Pushout

/-!
# Pushouts in the completed base category
-/

@[expose] public section

open CategoryTheory Limits CompleteLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- Lemma 90.4.3: the completed base category Ĉ_Λ = CompleteLocalAlgCat Λ k admits pushouts. -/
@[stacks 06SB]
instance hasPushouts : HasPushouts (CompleteLocalAlgCat Λ k) :=
  hasPushouts_of_hasColimit_span (CompleteLocalAlgCat Λ k)

end CompleteLocalAlgCat
