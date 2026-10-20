module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.RingTheory.RingHom.Perfect.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.FiniteCohomology
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.UpperShriek

variable {R A : Type u} [CommRing R] [CommRing A]
  [IsNoetherianRing R] [IsNoetherianRing A]

/-- The upper-shriek functor preserves the bounded-below derived subcategory. -/
theorem mapsBoundedBelow (f : R →+* A) (hf : f.FiniteType) (p : Presentation f) :
    (t.plus : ObjectProperty (DerivedCategory (ModuleCat.{u, u} R))) ≤
      (t.plus : ObjectProperty (DerivedCategory (ModuleCat.{u, u} A))).inverseImage
        p.functor := sorry

/-- The upper-shriek functor preserves bounded-below objects with finite cohomology. -/
theorem mapsBoundedBelowFiniteCohomology
    (f : R →+* A) (hf : f.FiniteType) (p : Presentation f) :
    ((t.plus : ObjectProperty (DerivedCategory (ModuleCat.{u, u} R))) ⊓
        DerivedCategory.cohomologyIn (ModuleCat.isFG R)) ≤
      ((t.plus : ObjectProperty (DerivedCategory (ModuleCat.{u, u} A))) ⊓
        DerivedCategory.cohomologyIn (ModuleCat.isFG A)).inverseImage p.functor := sorry

/-- A perfect finite-type map has upper-shriek preserving the bounded-above subcategory. -/
theorem mapsBoundedAboveOfPerfect
    (f : R →+* A) (hf : f.FiniteType) (p : Presentation f) [f.IsPerfectRingMap] :
    (t.minus : ObjectProperty (DerivedCategory (ModuleCat.{u, u} R))) ≤
      (t.minus : ObjectProperty (DerivedCategory (ModuleCat.{u, u} A))).inverseImage
        p.functor := sorry

/-- A perfect finite-type map has upper-shriek preserving bounded-above finite-cohomology objects. -/
theorem mapsBoundedAboveFiniteCohomologyOfPerfect
    (f : R →+* A) (hf : f.FiniteType) (p : Presentation f) [f.IsPerfectRingMap] :
    ((t.minus : ObjectProperty (DerivedCategory (ModuleCat.{u, u} R))) ⊓
        DerivedCategory.cohomologyIn (ModuleCat.isFG R)) ≤
      ((t.minus : ObjectProperty (DerivedCategory (ModuleCat.{u, u} A))) ⊓
        DerivedCategory.cohomologyIn (ModuleCat.isFG A)).inverseImage p.functor := sorry

/-- A perfect finite-type map has upper-shriek preserving bounded finite-cohomology objects. -/
theorem mapsBoundedFiniteCohomologyOfPerfect
    (f : R →+* A) (hf : f.FiniteType) (p : Presentation f) [f.IsPerfectRingMap] :
    ((t.bounded : ObjectProperty (DerivedCategory (ModuleCat.{u, u} R))) ⊓
        DerivedCategory.cohomologyIn (ModuleCat.isFG R)) ≤
      ((t.bounded : ObjectProperty (DerivedCategory (ModuleCat.{u, u} A))) ⊓
        DerivedCategory.cohomologyIn (ModuleCat.isFG A)).inverseImage p.functor := sorry

end CategoryTheory.ModuleCat.UpperShriek
