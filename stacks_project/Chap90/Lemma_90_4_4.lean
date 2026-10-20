module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.TensorProduct
import StacksCheckRecall

/-!
# Coproducts of pairs in the completed base category
-/

@[expose] public section

open CategoryTheory Limits

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 90.4.4: the completed base category Ĉ_Λ = CompleteLocalAlgCat Λ k admits
coproducts of pairs of objects. -/
@[stacks 06H1] #check (CompleteLocalAlgCat.hasBinaryCoproducts :
  HasBinaryCoproducts (CompleteLocalAlgCat Λ k))
