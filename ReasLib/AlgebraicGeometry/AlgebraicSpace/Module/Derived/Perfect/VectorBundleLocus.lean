module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.VectorBundle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction

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
  OpenSubspace.fromOpens (IsPerfect.vectorBundleLocusPoints hE i r)

/-- The underlying point-set of `vectorBundleLocus` is `vectorBundleLocusPointsSet`. -/
theorem IsPerfect.vectorBundleLocus_pointsSet_eq (hE : IsPerfect E) (i r : ℤ) :
    (IsPerfect.vectorBundleLocus hE i r).pointsSet =
      IsPerfect.vectorBundleLocusPointsSet E i r :=
  OpenSubspace.fromOpens_pointsSet (IsPerfect.vectorBundleLocusPoints hE i r)

/-- A point of `|X|` lies in the vector-bundle locus if and only if it belongs to an open
subspace on which the étale restriction of `E` is a rank-`r` vector bundle in degree `i`. -/
theorem IsPerfect.mem_vectorBundleLocus_iff (hE : IsPerfect E) (i r : ℤ) (x : Points X) :
    x ∈ (IsPerfect.vectorBundleLocus hE i r).pointsSet ↔
      ∃ U : OpenSubspace X, x ∈ U.pointsSet ∧
        IsVectorBundleOfRankInDegree ((pullback U.ι).obj E) i r := by
  rw [IsPerfect.vectorBundleLocus_pointsSet_eq]
  rfl

/-- For every integer degree and rank, the restriction to the canonical vector-bundle
locus is a vector bundle of that rank in that degree, and a morphism factors through the
locus exactly when its derived pullback is such a vector bundle. -/
theorem IsPerfect.vectorBundleLocus_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    {E : ModuleDerived X} (hE : IsPerfect E) (i r : ℤ) :
    IsVectorBundleOfRankInDegree
        ((pullback (IsPerfect.vectorBundleLocus hE i r).ι).obj E) i r ∧
      ∀ {Y : AlgebraicSpace S} (f : Y ⟶ X),
        (∃ g : Y ⟶ (IsPerfect.vectorBundleLocus hE i r).X,
            g ≫ (IsPerfect.vectorBundleLocus hE i r).ι = f) ↔
          IsVectorBundleOfRankInDegree ((pullback f).obj E) i r :=
  sorry

/-- A morphism factors through the vector-bundle locus if and only if the derived pullback
is a rank-`r` vector bundle placed in degree `i`. -/
theorem IsPerfect.vectorBundleLocus_factor_iff (hE : IsPerfect E) (i r : ℤ)
    {Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (∃ g : Y ⟶ (IsPerfect.vectorBundleLocus hE i r).X,
        g ≫ (IsPerfect.vectorBundleLocus hE i r).ι = f) ↔
      IsVectorBundleOfRankInDegree ((pullback f).obj E) i r :=
  (IsPerfect.vectorBundleLocus_spec hE i r).2 f

/-- The vector-bundle locus has empty point set when the prescribed integer rank is negative. -/
theorem IsPerfect.vectorBundleLocusPointsSet_eq_empty (hE : IsPerfect E) (i r : ℤ)
    (hr : r < 0) :
    IsPerfect.vectorBundleLocusPointsSet E i r = ∅ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
