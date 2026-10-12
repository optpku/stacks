/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal.AssociatedGraded
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Regularity
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Conormal

/-!
# Conormal criteria for ideal sheaves

This file defines the canonical conormal module of an ideal sheaf and states finite local
freeness and associated graded comparison criteria for ideal sheaves on ringed spaces.
-/

@[expose] public section

open AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- The conormal module of an ideal sheaf is the degree-one part of the associated graded
algebra of the canonical quotient projection. -/
noncomputable def idealConormalModule (I : IdealSubobject X) :=
  (KernelIdeal.AssociatedGraded.algebra (IdealSheaf.Quotient.projection I)).obj 1

/-- An ideal sheaf has finite locally free conormal module when its canonical conormal module
over the quotient structure sheaf is finite locally free. -/
def idealSheafConormalFiniteLocallyFreeCriterion (I : IdealSubobject X) : Prop :=
  SheafOfModules.IsFiniteLocallyFree (idealConormalModule I)

/-- The conormal criterion is precisely finite local freeness of the canonical conormal module
over the quotient structure sheaf. -/
theorem idealSheafConormalFiniteLocallyFreeCriterion_iff (I : IdealSubobject X) :
    idealSheafConormalFiniteLocallyFreeCriterion I ↔
      SheafOfModules.IsFiniteLocallyFree (idealConormalModule I) := Iff.rfl

/-- An ideal sheaf satisfies the associated-graded polynomial criterion when the canonical
conormal-algebra map of every stalk ideal is bijective. -/
def idealSheafAssociatedGradedPolynomialCriterion (I : IdealSubobject X) : Prop :=
  ∀ x : X, Function.Bijective (idealConormalAlgebraQuotient (idealSheafStalkIdeal I x))

/-- The associated-graded criterion is precisely stalkwise bijectivity of the canonical
conormal-algebra maps. -/
theorem idealSheafAssociatedGradedPolynomialCriterion_iff (I : IdealSubobject X) :
    idealSheafAssociatedGradedPolynomialCriterion I ↔
      ∀ x : X,
        Function.Bijective
          (idealConormalAlgebraQuotient (idealSheafStalkIdeal I x)) := Iff.rfl

end AlgebraicGeometry.RingedSpace
