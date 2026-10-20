module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.PhSpectralSequence
import StacksCheckRecall

/-!
# Lemma 85.36.6

A ph hypercovering `a : U ⟶ X` of an algebraic space over a scheme gives a
canonical spectral sequence for every abelian étale sheaf `F`, with
`E₁^{p,q} = H^q_étale(U_p, F_p)` converging to `H^{p+q}_étale(X, F)`.
Here `F_p` is the spaces-étale pullback along `a.app (op ⦋p⦌)`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor FilteredComplex.SpectralSequence.Realization

/- Lemma 85.36.6. A ph hypercovering gives the stage-cohomology spectral
sequence converging to the étale cohomology of the augmentation target. -/
@[stacks 0DHP] #check
  (AlgebraicGeometry.AlgebraicSpace.Simplicial.exists_spectralSequence :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {U : SimplicialObject (AlgebraicSpace S)}
      (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
      (ha : (SimplicialObject.Augmentation.toAugmented a).IsHypercovering (phTopology S))
      (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}),
      ∃ E : WithAbutment (fun n ↦ plusCohomology X n) F,
        Nonempty (∀ p q : ℤ,
          (E.sequence.page 1).X (p, q) ≅ (pageOneFunctor a p q).obj F))
