module

public import stacks_project.Chap85.Lemma_85_29_2_Quasicoherent
public import stacks_project.Chap85.Lemma_85_29_2_Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 85.29.2

The category of quasi-coherent modules on a groupoid scheme is equivalent to the
category of quasi-coherent modules on the Zariski site of the associated simplicial scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Lemma 85.29.2
Let `S` be a scheme. Let `(U, R, s, t, c)` be a groupoid scheme over `S`. Let `X` be the
simplicial scheme over `S` constructed in Lemma 85.29.1. Then the category of quasi-coherent
modules on `(U, R, s, t, c)` is equivalent to the category of quasi-coherent modules on
`X_Zar`. -/
@[stacks 07TP]
def quasiCoherentZariskiEquivalence {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.QCoh ≌ SimplicialObject.QCoh G.simplicialScheme :=
  zariskiQCohEquivalence G

end AlgebraicGeometry.GroupoidScheme
