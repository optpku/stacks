/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_8_4_Coproduct
public import stacks_project.Chap71.Lemma_71_5_6_Locus

/-!
# The flat locus of a module on an algebraic space

The coproduct of the successive Fitting rank loci of a finite-type
quasi-coherent module on an algebraic space, together with its structure
morphism to the ambient space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The coproduct of all successive Fitting rank loci of a module on an
algebraic space. -/
noncomputable abbrev fittingFlatLocus {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] : AlgebraicSpace S :=
  coproduct fun r : ℕ ↦ (fittingRankLocus F r).X

/-- The canonical morphism from the coproduct of the Fitting rank loci to the
ambient algebraic space. -/
noncomputable abbrev fittingFlatLocusι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    fittingFlatLocus F ⟶ X :=
  coproductDesc fun r : ℕ ↦ (fittingRankLocus F r).ι

/-- Postcomposing a rank-locus inclusion with the structure map of the Fitting
flat locus recovers the rank-locus immersion. -/
theorem fittingRankLocus_ι_comp_fittingFlatLocusι {S : Scheme.{u}}
    {X : AlgebraicSpace S} (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (r : ℕ) :
    coproductι (fun n : ℕ ↦ (fittingRankLocus F n).X) r ≫ fittingFlatLocusι F =
      (fittingRankLocus F r).ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
