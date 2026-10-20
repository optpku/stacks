module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic

/-!
# Field-extension base change in over categories

This leaf packages the canonical field-extension pullback as an object of the
appropriate over category.  The underlying scheme and its morphism to the new
base are owned by `FieldExtension`; this file supplies only the slice-category
presentation and the projection to the source scheme.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Over

/-- The canonical pullback functor on schemes over a field spectrum along a field extension. -/
abbrev functor
    (k K : Type u) [Field k] [Field K] [Algebra k K] :
    CategoryTheory.Over (Spec (CommRingCat.of k)) ⥤
      CategoryTheory.Over (Spec (CommRingCat.of K)) :=
  CategoryTheory.Over.pullback (FieldExtension.specMap k K)

/-- The field-extension base change of a scheme over `Spec k`, viewed over `Spec K`. -/
abbrev baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Over (Spec (CommRingCat.of k))) : Over (Spec (CommRingCat.of K)) :=
  (functor k K).obj X

/-- The projection from a field-extension base change in `Over (Spec K)` to its source scheme. -/
abbrev toSource
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Over (Spec (CommRingCat.of k))) :
    (baseChange k K X).left ⟶ X.left :=
  FieldExtension.toSource k K X.hom

/-- Field-extension base change transports the canonical group-object structure. -/
instance instGrpObj
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Over (Spec (CommRingCat.of k))) [GrpObj X] :
    GrpObj (baseChange k K X) :=
  ((functor k K).mapGrp.obj (.mk X)).grp

end FieldExtension.Over

end AlgebraicGeometry
