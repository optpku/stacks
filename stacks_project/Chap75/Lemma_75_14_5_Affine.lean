module

public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap75.Definition_75_14_2_Approximation

/-!
# Affine approximation by perfect complexes on algebraic spaces

On an algebraic space representable by an affine scheme, `m`-pseudo-coherent
objects of `DerivedQCoh` whose cohomology is supported on a closed subset from
degree `m - r + 1` onward admit a perfect approximation through degree `m` when
the complement is a union of `r` affine opens. In particular, approximation by
perfect complexes holds on every affine algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace AffineOpenCover

/-- An algebraic space has an affine open cover of cardinality `t` if it is the
union of `t` affine open subspaces. -/
def HasCard {S : Scheme.{u}} (X : AlgebraicSpace S) (t : ℕ) : Prop :=
  ∃ U : Fin t → OpenSubspace X, (∀ i, IsAffine (U i).X) ∧ ⋃ i, (U i).pointsSet = Set.univ

/-- `HasCard X t` is a cover of `X` by `t` affine open subspaces. -/
theorem hasCard_iff {S : Scheme.{u}} (X : AlgebraicSpace S) (t : ℕ) :
    HasCard X t ↔
      ∃ U : Fin t → OpenSubspace X,
        (∀ i, IsAffine (U i).X) ∧ ⋃ i, (U i).pointsSet = Set.univ := sorry

end AffineOpenCover

namespace HasPerfectApproximation

/-- On an affine algebraic space, an `m`-pseudo-coherent object of `DerivedQCoh`
whose cohomology is supported on `T` from degree `m - r + 1` onward has a
perfect approximation through degree `m` when the complement of `T` is a union
of `r` affine opens. -/
theorem of_isAffine {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAffine X]
    (T : Closeds (Points X)) (E : DerivedQCoh X) (m : ℤ) (r : ℕ)
    (h_cover : AffineOpenCover.HasCard (OpenSubspace.ofOpensSpace T.compl) r)
    (h_pseudoCoherent : IsMPseudoCoherent X E.obj m)
    (h_support : ∀ i : ℤ, m - (r : ℤ) + 1 ≤ i →
      Modules.moduleSupportedOn (T : Set (Points X))
        ((DerivedCategory.homologyFunctor (Modules X) i).obj E.obj)) :
    HasPerfectApproximation T E m := sorry

end HasPerfectApproximation

namespace HasApproximationByPerfectComplexes

/-- Every affine algebraic space admits approximation by perfect complexes. -/
theorem of_isAffine {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAffine X] :
    HasApproximationByPerfectComplexes X := sorry

end HasApproximationByPerfectComplexes

end AlgebraicGeometry.AlgebraicSpace
