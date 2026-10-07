module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.Preservation
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.UpperShriek

variable {R A : Type u} [CommRing R] [CommRing A]
  [IsNoetherianRing R] [IsNoetherianRing A]

/- Lemma 47.24.2 (1): upper-shriek preserves bounded-below derived objects. -/
@[stacks 0BZK] #check (CategoryTheory.ModuleCat.UpperShriek.mapsBoundedBelow :
  ∀ (f : R →+* A) (hf : f.FiniteType) (p : Presentation f),
    (t.plus : ObjectProperty (DerivedCategory (ModuleCat.{u, u} R))) ≤
      (t.plus : ObjectProperty (DerivedCategory (ModuleCat.{u, u} A))).inverseImage
        p.functor)

/- Lemma 47.24.2 (2): upper-shriek preserves bounded-below objects with finite cohomology. -/
@[stacks 0BZK] #check (CategoryTheory.ModuleCat.UpperShriek.mapsBoundedBelowFiniteCohomology :
  ∀ (f : R →+* A) (hf : f.FiniteType) (p : Presentation f),
    ((t.plus : ObjectProperty (DerivedCategory (ModuleCat.{u, u} R))) ⊓
        DerivedCategory.cohomologyIn (ModuleCat.isFG R)) ≤
      ((t.plus : ObjectProperty (DerivedCategory (ModuleCat.{u, u} A))) ⊓
        DerivedCategory.cohomologyIn (ModuleCat.isFG A)).inverseImage p.functor)

/- Lemma 47.24.2 (3): perfect upper-shriek preserves bounded-above objects. -/
@[stacks 0BZK] #check (CategoryTheory.ModuleCat.UpperShriek.mapsBoundedAboveOfPerfect :
  ∀ (f : R →+* A) (hf : f.FiniteType) (p : Presentation f) [f.IsPerfectRingMap],
    (t.minus : ObjectProperty (DerivedCategory (ModuleCat.{u, u} R))) ≤
      (t.minus : ObjectProperty (DerivedCategory (ModuleCat.{u, u} A))).inverseImage
        p.functor)

/- Lemma 47.24.2 (4): perfect upper-shriek preserves bounded-above finite-cohomology objects. -/
@[stacks 0BZK] #check (CategoryTheory.ModuleCat.UpperShriek.mapsBoundedAboveFiniteCohomologyOfPerfect :
  ∀ (f : R →+* A) (hf : f.FiniteType) (p : Presentation f) [f.IsPerfectRingMap],
    ((t.minus : ObjectProperty (DerivedCategory (ModuleCat.{u, u} R))) ⊓
        DerivedCategory.cohomologyIn (ModuleCat.isFG R)) ≤
      ((t.minus : ObjectProperty (DerivedCategory (ModuleCat.{u, u} A))) ⊓
        DerivedCategory.cohomologyIn (ModuleCat.isFG A)).inverseImage p.functor)

/- Lemma 47.24.2 (5): perfect upper-shriek preserves bounded finite-cohomology objects. -/
@[stacks 0BZK] #check (CategoryTheory.ModuleCat.UpperShriek.mapsBoundedFiniteCohomologyOfPerfect :
  ∀ (f : R →+* A) (hf : f.FiniteType) (p : Presentation f) [f.IsPerfectRingMap],
    ((t.bounded : ObjectProperty (DerivedCategory (ModuleCat.{u, u} R))) ⊓
        DerivedCategory.cohomologyIn (ModuleCat.isFG R)) ≤
      ((t.bounded : ObjectProperty (DerivedCategory (ModuleCat.{u, u} A))) ⊓
        DerivedCategory.cohomologyIn (ModuleCat.isFG A)).inverseImage p.functor)

end CategoryTheory.ModuleCat.UpperShriek
