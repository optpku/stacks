/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Additive
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of complexes of modules on a ringed space

Taking stalks is functorial in a module sheaf.  This file exposes the induced functor and its
evaluation on homological complexes without fixing an indexing type or complex shape.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type v}

/-- Taking stalks preserves zero morphisms.  This instance lets homological-complex mapping be
inferred without rebuilding a proof at each use site. -/
@[stacks 0GT6 "stalks preserve zero morphisms", instance]
instance stalkModuleFunctor_preservesZeroMorphisms (x : X) :
    (stalkModuleFunctor x).PreservesZeroMorphisms := sorry

/-- The functor taking a complex of module sheaves to its complex of stalk modules at `x`. -/
@[stacks 0GT6 "stalk functor on complexes"]
abbrev stalkComplexFunctor (c : ComplexShape ι) (x : X) :
    HomologicalComplex X.Modules c ⥤
      HomologicalComplex (ModuleCat (X.presheaf.stalk x)) c :=
  (stalkModuleFunctor x).mapHomologicalComplex c

/-- The complex of stalk modules of `K` at `x`. -/
@[stacks 0GT6 "stalk complex"]
abbrev stalkComplex (K : HomologicalComplex X.Modules c) (x : X) :
    HomologicalComplex (ModuleCat (X.presheaf.stalk x)) c :=
  (stalkComplexFunctor c x).obj K

/-- The stalk-complex construction is evaluation of the mapped homological-complex functor. -/
@[simp]
theorem stalkComplex_eq_mapHomologicalComplex_obj
    (K : HomologicalComplex X.Modules c) (x : X) :
    stalkComplex K x = ((stalkModuleFunctor x).mapHomologicalComplex c).obj K := sorry

end AlgebraicGeometry.RingedSpace
