module

public import ReasLib.AlgebraicGeometry.ChowGroup.Relative
public import ReasLib.AlgebraicGeometry.ChowGroup.Reindex

/-!
# Reindexing relative Chow groups

The relative Chow group `RelativeChow delta X k` is the Chow group of `X.left` graded by the
induced relative dimension function. This file specializes `ChowGroup.reindex` to it, so that
callers transport classes between equal grading indices without pinning the
`IsLocallyNoetherian` instance coming from local finite type over `S`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeChow

/-- Transport a relative Chow group along an equality of grading indices; this is
`ChowGroup.reindex` for the relative dimension function. -/
noncomputable def castDegree
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {m n : ℤ} (h : m = n) :
    RelativeChow delta X m →+ RelativeChow delta X n :=
  (@ChowGroup.reindex X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
    (X.hom.relativeDimensionFunction delta) inferInstance m n h).toAddMonoidHom

/-- Reindexing by a degree equality sends each relative Chow class to its transported value. -/
theorem castDegree_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {m n : ℤ} (h : m = n)
    (alpha : RelativeChow delta X m) : castDegree delta h alpha = h ▸ alpha := sorry

/-- Reindexing along a reflexive degree equality is the identity. -/
theorem castDegree_rfl
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] (m : ℤ) :
    castDegree delta (X := X) (rfl : m = m) = AddMonoidHom.id _ := sorry

end AlgebraicGeometry.RelativeChow
