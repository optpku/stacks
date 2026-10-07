module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelianYoneda

/-!
# Degree-zero sheaf cohomology

Objectwise degree-zero sheaf cohomology is canonically identified with ordinary sections.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]

/-- Degree-zero cohomology over an object of a site is additively equivalent to evaluation of
the coefficient sheaf at that object. -/
noncomputable def cohomologyZeroEquivSections
    (F : Sheaf J AddCommGrpCat.{v}) (U : C) :
    F.H' 0 U ≃+ F.obj.obj (op U) :=
  Abelian.Ext.addEquiv₀.trans
    (GrothendieckTopology.FreeAbelianYoneda.homAddEquiv J U F)

/-- The degree-zero cohomology equivalence is natural in the coefficient sheaf. -/
theorem cohomologyZeroEquivSections_naturality
    {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (U : C) (x : F.H' 0 U) :
    cohomologyZeroEquivSections J G U
        (((cohomologyPresheafFunctor J 0).map f).app (op U) x) =
      f.hom.app (op U) (cohomologyZeroEquivSections J F U x) := sorry

end CategoryTheory.Sheaf
