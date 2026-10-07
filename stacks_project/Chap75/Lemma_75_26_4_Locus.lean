module

public import stacks_project.Chap66.Lemma_66_20_1_Sheaf
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_26_4_Pullback
public import stacks_project.Chap75.Lemma_75_26_4_VectorBundle

/-!
# Vector-bundle locus of a perfect derived module on an algebraic space

The canonical open subspace of `X` on which a perfect object of `D(𝒪_X)` is a finite
locally free module of fixed rank placed in a single degree.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X}

/-- The set of points of `|X|` that lie in some open subspace on which `E` is a vector
bundle of rank `r` in degree `i`. -/
def IsPerfect.vectorBundleLocusPointsSet (E : ModuleDerived X) (i r : ℤ) : Set (Points X) :=
  {x | ∃ U : OpenSubspace X, x ∈ U.pointsSet ∧
    IsVectorBundleOfRankInDegree ((pullback U.ι).obj E) i r}

/-- For a perfect derived module, the rank-`r` degree-`i` vector-bundle locus is open. -/
theorem IsPerfect.isOpen_vectorBundleLocusPointsSet (hE : IsPerfect E) (i r : ℤ) :
    IsOpen (IsPerfect.vectorBundleLocusPointsSet E i r) :=
  sorry

/-- The rank-`r` degree-`i` vector-bundle locus as an open of `|X|`. -/
def IsPerfect.vectorBundleLocusPoints (hE : IsPerfect E) (i r : ℤ) : Opens (Points X) :=
  Opens.mk (IsPerfect.vectorBundleLocusPointsSet E i r)
    (IsPerfect.isOpen_vectorBundleLocusPointsSet hE i r)

/-- The canonical open subspace on which a perfect derived module is a vector bundle of
rank `r` placed in degree `i`. -/
def IsPerfect.vectorBundleLocus (hE : IsPerfect E) (i r : ℤ) : OpenSubspace X :=
  OpenSubspace.ofOpens (IsPerfect.vectorBundleLocusPoints hE i r)

/-- The underlying point-set of `vectorBundleLocus` is `vectorBundleLocusPointsSet`. -/
theorem IsPerfect.vectorBundleLocus_pointsSet_eq (hE : IsPerfect E) (i r : ℤ) :
    (IsPerfect.vectorBundleLocus hE i r).pointsSet =
      IsPerfect.vectorBundleLocusPointsSet E i r :=
  sorry

/-- A point of `|X|` lies in the vector-bundle locus if and only if it belongs to an open
subspace on which the étale restriction of `E` is a rank-`r` vector bundle in degree `i`. -/
theorem IsPerfect.mem_vectorBundleLocus_iff (hE : IsPerfect E) (i r : ℤ) (x : Points X) :
    x ∈ (IsPerfect.vectorBundleLocus hE i r).pointsSet ↔
      ∃ U : OpenSubspace X, x ∈ U.pointsSet ∧
        IsVectorBundleOfRankInDegree ((pullback U.ι).obj E) i r :=
  sorry

/-- A morphism factors through the vector-bundle locus if and only if the derived pullback
is a rank-`r` vector bundle placed in degree `i`. Requires `0 ≤ r`, since otherwise the
rank-`r` property is unsatisfiable while the empty space still factors through the empty
locus. -/
theorem IsPerfect.vectorBundleLocus_factor_iff (hE : IsPerfect E) (i r : ℤ) (hr : 0 ≤ r)
    {Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (∃ g : Y ⟶ (IsPerfect.vectorBundleLocus hE i r).X,
        g ≫ (IsPerfect.vectorBundleLocus hE i r).ι = f) ↔
      IsVectorBundleOfRankInDegree ((modulePullbackDerived f).obj E) i r :=
  sorry

/-- For negative rank, no natural number realizes `r`, so the vector-bundle locus is empty. -/
theorem IsPerfect.vectorBundleLocusPointsSet_eq_empty (hE : IsPerfect E) (i r : ℤ)
    (hr : r < 0) :
    IsPerfect.vectorBundleLocusPointsSet E i r = ∅ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
