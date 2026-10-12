/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Abutment
public import stacks_project.Chap85.Lemma_85_33_2_Hypercovering
public import stacks_project.Chap85.Lemma_85_33_6_Cohomology

/-!
# Lemma 85.33.6

A first-quadrant spectral sequence with `E₁^{p,q} = H^q_étale(U_p, F_p)`
converging to `H^{p+q}_étale(X, F)`, for an fppf hypercovering of an algebraic
space.
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

/-- Lemma 85.33.6: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `U`
be a simplicial algebraic space over `S`. Let `a : U ⟶ X` be an augmentation. Let `F`
be an abelian sheaf on `X_étale`. Let `F_n` be the pullback to `U_n,étale`. If `a` is
an fppf hypercovering of `X`, then there is a canonical first-quadrant spectral
sequence with `E₁^{p,q} = H^q_étale(U_p, F_p)` converging to `H^{p+q}_étale(X, F)`. -/
@[stacks 0DHA]
theorem exists_etaleSpectralSequence (ha : IsFppfHypercovering a)
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          spacesEtaleCohomology (U.obj (op ⦋p⦌)) ((stageInverseImage a p).obj F) q),
      CohomologicalSpectralSequenceNat.ConvergesTo E (spacesEtaleCohomology X F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
