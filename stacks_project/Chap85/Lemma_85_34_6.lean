module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Abutment
public import stacks_project.Chap85.Lemma_85_34_6_Cohomology

/-!
# Lemma 85.34.6

A first-quadrant spectral sequence with `E₁^{p,q} = H^q_étale(U_p, F_p)`
converging to `H^{p+q}_étale(X, F)`, for an fppf hypercovering of an algebraic
space and a quasi-coherent `𝒪_X`-module.
-/

@[expose] public section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Lemma 85.34.6: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `U`
be a simplicial algebraic space over `S`. Let `a : U ⟶ X` be an augmentation. Let `F`
be a quasi-coherent `𝒪_X`-module. Let `F_n` be the pullback to `U_n,étale`. If `a` is
an fppf hypercovering of `X`, then there is a canonical first-quadrant spectral
sequence with `E₁^{p,q} = H^q_étale(U_p, F_p)` converging to `H^{p+q}_étale(X, F)`. -/
@[stacks 0DHH]
theorem exists_qcohEtaleSpectralSequence (ha : IsFppfHypercovering a)
    (F : (spacesQuasiCoherentModuleProperty X).FullSubcategory) :
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅ stageModuleCohomology a F.obj p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (spacesEtaleModuleCohomology X F.obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
