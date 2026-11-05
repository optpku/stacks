module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Presheaf

/-!
# Relative Picard fppf sheaf and its representations

Raw group-valued classes are owned by `Relative.Presheaf`. The explicit relative
quotient is exposed in `Relative.Quotient`; both precede representability.
This module keeps the established concrete sheafification model and unit, so
existing degree components and represented Picard schemes use the same data.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativePicard

/-- The relative Picard functor is the concrete fppf `plus-plus` sheafification
of `T ↦ Pic(T ×ₛ X)`. Use the same model and unit as the group-valued
sheafification and the degree subfunctors. The abstract chosen left adjoint
`presheafToSheaf` is only canonically isomorphic to this model. -/
noncomputable def functor {S : Scheme.{u}} (X : Over S) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (plusPlusSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj (presheaf X)

/-- The underlying presheaf of the relative Picard functor is the fppf sheafification of
`presheaf X`. -/
theorem functor_val {S : Scheme.{u}} (X : Over S) :
    (functor X).obj = (Scheme.fppfTopology.over S).sheafify (presheaf X) := rfl

/-- A chosen `S`-scheme representing the relative Picard functor. -/
noncomputable def scheme {S : Scheme.{u}} (X : Over S)
    [(functor X).obj.IsRepresentable] : Over S :=
  (functor X).obj.reprX

/-- The chosen relative Picard scheme represents the relative Picard functor. -/
noncomputable def schemeRepresentation {S : Scheme.{u}} (X : Over S)
    [(functor X).obj.IsRepresentable] :
    (functor X).obj.RepresentableBy (scheme X) :=
  (functor X).obj.representableBy

end AlgebraicGeometry.RelativePicard
