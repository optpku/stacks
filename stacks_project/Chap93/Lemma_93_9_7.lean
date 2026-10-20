module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Affine
public import ReasLib.AlgebraicGeometry.FormalDeformation.Stalk.Comparison
import StacksCheckRecall

/-!
# Affine scheme deformations versus algebra deformations
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable (Λ k P : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k] [CommRing P] [Algebra k P]

/- Lemma 93.9.7: Global sections give the natural equivalence between deformations
of `Spec(P)` and flat algebra deformations of `P`, over the same Artinian local base. -/
@[stacks 0DYX] #check (FlatSchemeCat.instIsEquivalence_globalSectionsBasedFunctor Λ k P :
  CategoryTheory.BasedFunctor.IsEquivalence (FlatSchemeCat.globalSectionsBasedFunctor Λ k P))
