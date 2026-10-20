module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AffineOver

/-!
# Finite affine families in affine scheme slices

This leaf turns a finite affine family over the source of an affine object of
`Over S` into explicit objects, arrows, and a presieve in `S.AffineOver`.
It is independent of a topology and is shared by standard-cover
presentations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AffineOver

/-- The `j`-th chart of an affine family over the source of `U`, regarded as
an affine object over the original base scheme. -/
def ofAffineFamilyObj {S : Scheme.{u}} (U : S.AffineOver)
    (family : AffineFamilyOver U.obj.left) (j : Fin family.n) : S.AffineOver :=
  AffineOver.mk _ (family.isAffine j) (family.map j ≫ U.obj.hom)

/-- The arrow from a chart of an affine family to its affine-slice target. -/
def ofAffineFamilyMap {S : Scheme.{u}} (U : S.AffineOver)
    (family : AffineFamilyOver U.obj.left) (j : Fin family.n) :
    ofAffineFamilyObj U family j ⟶ U :=
  AffineOver.homMk (family.map j) rfl

/-- The presieve on `U` represented by an affine family over the source of
`U`. -/
def ofAffineFamilyPresieve {S : Scheme.{u}} (U : S.AffineOver)
    (family : AffineFamilyOver U.obj.left) : Presieve U :=
  Presieve.ofArrows (ofAffineFamilyObj U family) (ofAffineFamilyMap U family)

/-- The underlying object in `Over S` of an affine-family chart is the
composite of its chart map with the structure map of `U`. -/
@[simp]
theorem ofAffineFamilyObj_obj {S : Scheme.{u}} (U : S.AffineOver)
    (family : AffineFamilyOver U.obj.left) (j : Fin family.n) :
    (ofAffineFamilyObj U family j).obj = Over.mk (family.map j ≫ U.obj.hom) := sorry

/-- Applying the affine-slice inclusion to an affine-family chart arrow
recovers the corresponding arrow in the over category. -/
@[simp]
theorem forget_ofAffineFamilyMap {S : Scheme.{u}} (U : S.AffineOver)
    (family : AffineFamilyOver U.obj.left) (j : Fin family.n) :
    (forget S).map (ofAffineFamilyMap U family j) = Over.homMk (family.map j) rfl := sorry

end AlgebraicGeometry.Scheme.AffineOver
