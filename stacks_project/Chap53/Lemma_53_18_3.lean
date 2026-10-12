/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.FiniteDescent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 53.18.3: if `X` is proper over a field `k` and has dimension at most one, and
`f : Y ⟶ X` is finite and restricts to a closed immersion over a dense open of `X`, then
`dim_k H¹(Y, 𝒪_Y) ≤ dim_k H¹(X, 𝒪_X)`. -/
@[stacks 0CE3] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteDescent.structureSheafH1Finrank_le :
    ∀ {k : Type u} [Field k] {X Y : Scheme.{u}},
      (p : X ⟶ Spec (CommRingCat.of k)) → [IsProper p] →
      (f : Y ⟶ X) → [IsFinite f] →
      topologicalKrullDim X ≤ 1 →
      (∃ U : X.Opens, Dense (U : Set X) ∧ IsClosedImmersion (f ∣_ U)) →
      Scheme.Hom.cohomologyFinrank (f ≫ p)
          (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) 1 ≤
        Scheme.Hom.cohomologyFinrank p
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) 1)
