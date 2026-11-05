/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Fppf

/-!
# Group-valued relative Picard functor before curve geometry

The additive fppf sheaf has its canonical owner in `Relative.Fppf`.
The group-valued functor is its multiplicative view; its underlying sets are
canonically isomorphic to the established type-valued sheafification.
Representability is used only to construct the represented group object.
No field, curve, rational point or degree-zero hypothesis is required.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.MonObj Opposite
open scoped MonoidalCategory

universe u

namespace AlgebraicGeometry.RelativePicard

/-- The group-valued fppf sheafification of the Picard presheaf. -/
noncomputable def groupFunctor {S : Scheme.{u}} (X : Over S) :
    (Over S)ᵒᵖ ⥤ GrpCat.{u + 1} :=
  (additiveFppfSheaf X).obj ⋙
    AddCommGrpCat.toCommGrp ⋙ forget₂ CommGrpCat GrpCat

/-- Forgetting the multiplicative presentation of `groupFunctor X` gives the underlying
type-valued functor of its additive sheafification. -/
noncomputable def groupFunctorToAdditiveForgetIso {S : Scheme.{u}} (X : Over S) :
    groupFunctor X ⋙ forget GrpCat ≅
      (additiveFppfSheaf X).obj ⋙ forget AddCommGrpCat :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- The type-valued sheafification used in `functor X` has the same underlying values as the
corresponding sheafification functor. -/
noncomputable def functorSheafificationIso {S : Scheme.{u}} (X : Over S) :
    ((Scheme.fppfTopology.over S).sheafification (Type (u + 1))).obj (presheaf X) ≅
      (functor X).obj :=
  eqToIso (functor_val X).symm

/-- Forgetting the group structure on `groupFunctor X` recovers the relative Picard functor. -/
noncomputable def groupFunctorForgetIso {S : Scheme.{u}} (X : Over S) :
    groupFunctor X ⋙ forget GrpCat ≅ (functor X).obj :=
  groupFunctorToAdditiveForgetIso X ≪≫
    (Scheme.fppfTopology.over S).sheafifyCompIso
      (forget AddCommGrpCat.{u + 1}) (groupPresheaf X) ≪≫
    (eqToIso ((Scheme.fppfTopology.over S).sheafification_obj
      (Type (u + 1)) (groupPresheaf X ⋙ forget AddCommGrpCat))).symm ≪≫
    ((Scheme.fppfTopology.over S).sheafification (Type (u + 1))).mapIso
      (groupPresheafForgetIso X) ≪≫ functorSheafificationIso X

/-- The relative Picard scheme represents the underlying functor of `groupFunctor X`. -/
noncomputable def groupRepresentation {S : Scheme.{u}} (X : Over S)
    [(functor X).obj.IsRepresentable] :
    (groupFunctor X ⋙ forget GrpCat).RepresentableBy (scheme X) :=
  (schemeRepresentation X).ofIso (groupFunctorForgetIso X).symm

/-- The canonical group-object structure on the relative Picard scheme. -/
@[implicit_reducible]
noncomputable def schemeGrpObj {S : Scheme.{u}} (X : Over S)
    [(functor X).obj.IsRepresentable] : GrpObj (scheme X) :=
  GrpObj.ofRepresentableBy (scheme X) (groupFunctor X) (groupRepresentation X)

end AlgebraicGeometry.RelativePicard
