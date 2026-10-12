/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap75.Lemma_75_10_5_Gamma
public import stacks_project.Chap75.Lemma_75_19_1_Instances

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- For a quasi-compact and quasi-separated algebraic space, the quasicoherent
coreflection of a derived module has uniformly bounded cohomological amplitude
on complexes whose affine-étale hypercohomology is bounded. -/
theorem rightAdjoint_bounds_of_affineEtaleHypercohomology
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    ∃ N : ℤ, ∀ (K : ModuleDerived X) (a b : ℤ),
      (∀ {U : AlgebraicSpace S} (φ : U ⟶ X) [IsAffine U] [Etale φ],
          ∀ i : ℤ, i ∉ Set.Icc a b →
            IsZero (cohomologyAb U ((restrictFunctorDerived φ).obj K) i)) →
        ((inclusion X).rightAdjoint.obj K).obj.IsGE a ∧
          ((inclusion X).rightAdjoint.obj K).obj.IsLE (b + N) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
