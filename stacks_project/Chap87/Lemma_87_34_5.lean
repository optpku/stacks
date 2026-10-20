module

import StacksCheckRecall
public import stacks_project.Chap87.Lemma_87_34_5_Comparison

/-! # Lemma 87.34.5

The opposite affine étale site of a McQuillan formal spectrum is equivalent to
completed étale algebras with continuous algebra homomorphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalRing
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {B : Type u} [CommRing B] [TopologicalSpace B]
  [TopologicalRing.IsWeaklyAdmissibleRing B] (hB : Spec (.of B) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]

/- Lemma 87.34.5. The opposite affine étale site of the reduction is equivalent
to completed étale algebras, with all continuous algebra homomorphisms. -/
@[stacks 0DEF]
#check (AlgebraicGeometry.FormalAlgebraicSpace.spfAffineEtaleOppEquiv hB :
  ∀ (R : FormalAlgebraicSpace.ReductionData (spf B hB).obj),
    Nonempty ((AlgebraicSpace.affineEtaleSite R.space)ᵒᵖ ≌ CommAlgCat.EtaleCompletion B))
