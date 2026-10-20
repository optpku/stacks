module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Pushout
import StacksCheckRecall

/-!
# Pushouts in the completed base category
-/

@[expose] public section

open CategoryTheory Limits CompleteLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 90.4.3: the completed base category Ĉ_Λ = CompleteLocalAlgCat Λ k admits pushouts. -/
@[stacks 06SB] #check (CompleteLocalAlgCat.hasPushouts : HasPushouts (CompleteLocalAlgCat Λ k))
