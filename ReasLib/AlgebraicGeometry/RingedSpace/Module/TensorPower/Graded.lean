/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Graded
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Monoid
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorPower.Multiplication
import Mathlib.Tactic.CrossRefAttribute

/-!
# Graded tensor powers on ringed spaces

This file is the geometric facade for the topology-independent graded tensor-power algebra.
`mon` is the canonical Mathlib monoid object in naturally graded module sheaves; `graded` retains
the sectionwise presentation used by the local-section and graded-module APIs.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.TensorPower

variable {X : RingedSpace.{u}}

/-- The naturally graded object whose degree `n` is the `n`th tensor-power sheaf. -/
@[stacks 01CF "graded object of tensor powers on a ringed space"]
noncomputable abbrev gradedObject (F : X.Modules) : GradedObject ℕ X.Modules :=
  SheafOfModules.RingedSite.TensorPower.gradedObject X.sheaf F

/-- Tensor powers as a functor to naturally graded module sheaves on `X`. -/
@[stacks 01CF "graded tensor-power functor on a ringed space"]
noncomputable abbrev gradedObjectFunctor (X : RingedSpace.{u}) :
    X.Modules ⥤ GradedObject ℕ X.Modules :=
  SheafOfModules.RingedSite.TensorPower.gradedObjectFunctor X.sheaf

/-- The tensor powers of a module sheaf, bundled as Mathlib's naturally graded monoid object. -/
@[stacks 01CF "bundled graded tensor algebra on a ringed space"]
noncomputable abbrev mon (F : X.Modules) : Mon (GradedObject ℕ X.Modules) :=
  SheafOfModules.RingedSite.TensorPower.mon X.sheaf F

/-- The tensor-algebra functor from module sheaves to naturally graded monoid objects. -/
@[stacks 01CF "graded tensor-algebra functor on a ringed space"]
noncomputable abbrev monFunctor (X : RingedSpace.{u}) :
    X.Modules ⥤ Mon (GradedObject ℕ X.Modules) :=
  SheafOfModules.RingedSite.TensorPower.monFunctor X.sheaf

/-- Forgetting multiplication from the ringed-space tensor-algebra functor recovers the graded
tensor-power functor. -/
@[stacks 01CF "underlying graded-object functor of a ringed-space tensor algebra"]
theorem monFunctor_comp_forget (X : RingedSpace.{u}) :
    monFunctor X ⋙ Mon.forget (GradedObject ℕ X.Modules) =
      gradedObjectFunctor X := sorry

/-- The tensor powers of a module sheaf in the sectionwise graded-algebra presentation. -/
@[stacks 01CF "graded tensor algebra on a ringed space"]
noncomputable abbrev graded (F : X.Modules) :
    SheafOfModules.RingedSite.GradedAlgebraSheaf
      (J := Opens.grothendieckTopology X) X.sheaf ℕ :=
  SheafOfModules.RingedSite.TensorPower.graded
    (J := Opens.grothendieckTopology X) X.sheaf F

/-- The Mathlib monoid-object and sectionwise ringed-space presentations have the same underlying
graded module sheaf. -/
@[stacks 01CF "comparison of ringed-space graded tensor-algebra presentations"]
theorem mon_X_eq_graded (F : X.Modules) :
    (mon F).X = (graded F).toGradedObject := sorry

end AlgebraicGeometry.RingedSpace.TensorPower
