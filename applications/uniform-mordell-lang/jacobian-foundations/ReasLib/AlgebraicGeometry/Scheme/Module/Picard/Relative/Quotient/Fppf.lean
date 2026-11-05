module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Quotient
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Fppf

/-!
# The raw and relative-quotient presentations of the Picard fppf sheaf

This file constructs the sheafified quotient projection and the universal
property of the quotient fppf sheaf. Its being an isomorphism requires the
local triviality theorem for base line bundles. That proof obligation is
recorded separately in the comparison proposal; no isomorphism instance is
postulated here.

This interface works over any base and needs neither a section nor a theorem
asserting that a Picard scheme exists. It is shared by descent, relative
moduli, and arithmetic applications where the source has no rational point.
-/

@[expose] public section

open CategoryTheory
noncomputable section
universe u

namespace AlgebraicGeometry.RelativePicard

/-- The group-valued fppf sheaf of relative quotient classes. -/
noncomputable def quotientFppfSheaf {S : Scheme.{u}} (X : Over S) :
    Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} :=
  (plusPlusSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj
    (quotientPresheaf X)

/-- The canonical comparison, obtained by sheafifying the quotient projection. -/
noncomputable def toQuotientFppfSheaf {S : Scheme.{u}} (X : Over S) :
    additiveFppfSheaf X ⟶ quotientFppfSheaf X :=
  (plusPlusSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).map
    (toQuotientPresheaf X)

/-- The canonical map from relative quotient classes to their fppf sheafification. -/
noncomputable def toQuotientFppfSheafUnit {S : Scheme.{u}} (X : Over S) :
    quotientPresheaf X ⟶ (quotientFppfSheaf X).obj :=
  (Scheme.fppfTopology.over S).toSheafify (quotientPresheaf X)

/-- Maps out of the quotient Picard sheaf are determined by maps of quotient classes. -/
noncomputable def quotientFppfSheafHomEquiv {S : Scheme.{u}} (X : Over S)
    (F : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}) :
    (quotientFppfSheaf X ⟶ F) ≃ (quotientPresheaf X ⟶ F.obj) :=
  (plusPlusAdjunction (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).homEquiv
    (quotientPresheaf X) F

/-- The universal property uses the same concrete unit as the quotient sheaf. -/
@[simp]
theorem quotientFppfSheafHomEquiv_apply {S : Scheme.{u}} (X : Over S)
    (F : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})
    (g : quotientFppfSheaf X ⟶ F) :
    quotientFppfSheafHomEquiv X F g = toQuotientFppfSheafUnit X ≫ g.hom := rfl

end AlgebraicGeometry.RelativePicard
