module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearProjection.GeneralPosition
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/- Lemma 43.23.2 (1): if a closed subvariety `X ⊆ ℙ(V)` has dimension less than
`n - 1` and `x` is nonsingular, then on a nonempty open locus of closed projection
centers the induced map from `X` to its scheme-theoretic image is an isomorphism over
an open neighborhood of the image of `x`. -/
@[stacks 0B1Q] #check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearProjection.exists_open_isIso_toImage_restrict_near :
    ∀ (n : ℕ), Module.finrank k V = n + 1 →
      ∀ (X : SchemeOverField k) [Variety X]
        (i : X ⟶ Over.mk (ProjectiveSpace.VectorSpace.toSpec k V))
        [IsClosedImmersion i.left]
        (x : X.left), X.hom.SmoothAt x →
          topologicalKrullDim X.left < (n - 1 : ℕ) →
            ∀ (projection : ∀ (p : ProjectiveSpace.VectorSpace.scheme k V),
              IsClosed ({p} : Set (ProjectiveSpace.VectorSpace.scheme k V)) →
                ProjectiveSpace.VectorSpace.LinearProjection k V p),
              ∃ U : (ProjectiveSpace.VectorSpace.scheme k V).Opens, Nonempty U ∧
                ∀ (p : ProjectiveSpace.VectorSpace.scheme k V), p ∈ U →
                  (hp : IsClosed ({p} : Set (ProjectiveSpace.VectorSpace.scheme k V))) →
                    p ∉ Set.range i.left.base ∧
                      ∀ hpi : p ∉ Set.range i.left.base,
                        let f := (projection p hp).restrict i.left
                          ((projection p hp).range_subset_domain i.left hpi)
                        ∃ R : f.image.Opens,
                          f.toImage x ∈ R ∧ IsIso (f.toImage ∣_ R))

/- Lemma 43.23.2 (2): if a closed subvariety `X ⊆ ℙ(V)` has dimension `n - 1`
and `x` is nonsingular, then on a nonempty open locus of closed projection centers
the restricted projection is étale at `x`. -/
@[stacks 0B1Q] #check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearProjection.exists_open_etaleAt_restrict :
    ∀ (n : ℕ), Module.finrank k V = n + 1 →
      ∀ (X : SchemeOverField k) [Variety X]
        (i : X ⟶ Over.mk (ProjectiveSpace.VectorSpace.toSpec k V))
        [IsClosedImmersion i.left]
        (x : X.left), X.hom.SmoothAt x →
          topologicalKrullDim X.left + 1 = n →
            ∀ (projection : ∀ (p : ProjectiveSpace.VectorSpace.scheme k V),
              IsClosed ({p} : Set (ProjectiveSpace.VectorSpace.scheme k V)) →
                ProjectiveSpace.VectorSpace.LinearProjection k V p),
              ∃ U : (ProjectiveSpace.VectorSpace.scheme k V).Opens, Nonempty U ∧
                ∀ (p : ProjectiveSpace.VectorSpace.scheme k V), p ∈ U →
                  (hp : IsClosed ({p} : Set (ProjectiveSpace.VectorSpace.scheme k V))) →
                    p ∉ Set.range i.left.base ∧
                      ∀ hpi : p ∉ Set.range i.left.base,
                        ((projection p hp).restrict i.left
                          ((projection p hp).range_subset_domain i.left hpi)).EtaleAt x)
