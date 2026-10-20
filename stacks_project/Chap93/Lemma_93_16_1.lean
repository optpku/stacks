module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Unobstructed
import StacksCheckRecall

/-!
# Unobstructed deformation category of a local complete intersection

If `P` is a local complete intersection over the residue field `k`, then the
deformation category `Def_P` of Example 93.8.1 is unobstructed.
-/

@[expose] public section

universe u

/- Lemma 93.16.1: The flat-deformation category of a local complete intersection
over the residue field is unobstructed. -/
@[stacks 0DZH] #check (FlatAlgebraCat.instIsUnobstructed_deformationCategory :
  ∀ (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (P : Type u) [CommRing P] [Algebra k P]
    [IsLocalCompleteIntersection k P],
    CategoryTheory.Functor.IsUnobstructed (FlatAlgebraCat.deformationForget Λ k P))
