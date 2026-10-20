/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower.Graded.Functor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.SymmetricPower.Graded
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of the graded symmetric algebra on a ringed space

This facade specializes the topology-independent graded symmetric algebra functor. The underlying
graded algebra remains available from the narrower `SymmetricPower.Graded` facade.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.SymmetricPower

/-- A module-sheaf morphism induces a homomorphism of graded symmetric algebra sheaves. -/
@[stacks 01CF "functoriality of the symmetric algebra sheaf"]
noncomputable abbrev gradedMap {X : RingedSpace.{u}} {F G : X.Modules}
    (f : F ⟶ G) : graded F ⟶ graded G :=
  SheafOfModules.RingedSite.SymmetricPower.gradedMap
    (J := Opens.grothendieckTopology X) X.sheaf f

/-- The graded symmetric algebra functor on module sheaves over a ringed space. -/
@[stacks 01CF "symmetric algebra sheaf functor"]
noncomputable abbrev gradedFunctor (X : RingedSpace.{u}) :
    X.Modules ⥤ SheafOfModules.RingedSite.GradedAlgebraSheaf
      (J := Opens.grothendieckTopology X) X.sheaf ℕ :=
  SheafOfModules.RingedSite.SymmetricPower.gradedFunctor
    (J := Opens.grothendieckTopology X) X.sheaf

end AlgebraicGeometry.RingedSpace.SymmetricPower
