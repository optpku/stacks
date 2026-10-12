/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment
public import stacks_project.Chap85.Lemma_85_36_2_Hypercovering
public import stacks_project.Chap85.Lemma_85_36_6_Cohomology

/-!
# Lemma 85.36.6

If `a : U ⟶ X` is a proper hypercovering of an algebraic space `X` over a scheme
`S`, then an abelian sheaf `F` on `X_étale` has a cohomological spectral sequence
with `E₁^{p,q} = H^q_étale(U_p, F_p)` converging to `H^{p+q}_étale(X, F)`, where
`F_p` is the spaces-étale pullback of `F` along `a.app (op ⦋p⦌)`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor FilteredComplex.SpectralSequence.Realization
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Lemma 85.36.6. Let `S` be a scheme, `X` an algebraic space over `S`, `U` a
simplicial algebraic space over `S`, and `a : U ⟶ X` an augmentation. Let `F` be
an abelian sheaf on `X_étale`, and write `F_n` for its pullback to `U_n,étale`.
If `a` is a proper hypercovering of `X` (the ph-hypercovering case of this
section: proper surjective maps are ph covers), then there is a canonical
spectral sequence with `E₁^{p,q} = H^q_étale(U_p, F_p)` converging to
`H^{p+q}_étale(X, F)`. -/
@[stacks 0DHP]
theorem exists_spectralSequence (ha : IsProperHypercovering a)
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :
    ∃ S : WithAbutment (fun n ↦ plusCohomology X n) F,
      Nonempty (∀ p q : ℤ,
        (S.sequence.page 1).X (p, q) ≅ (pageOneFunctor a p q).obj F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
