/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.QuasiIso
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction.Derived.Basic
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.FromModules
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Objects of Differential Graded Bimodules

This leaf owns both derived-category interpretations of a differential graded bimodule:

* its full bimodule object, obtained by localizing modules over the enveloping DGA;
* its underlying right-module object, obtained after forgetting the left action.

The separate names prevent the right-module object used by Morita kernels from being confused
with the full bimodule object used by Hochschild cohomology.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory DifferentialGradedCategory

namespace DifferentialGradedBimodule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}

namespace Derived

/-- The derived category of differential graded `(A, B)`-bimodules, canonically modeled as the
derived category of right modules over `A.opposite ⊗[R] B`. -/
@[stacks 09ST "derived category of differential graded bimodules"]
abbrev Category (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) :=
  DifferentialGradedModule.Derived.Category.{u, v, max w x}
    (CochainDGAlgebra.enveloping A B)

/-- The canonical localization from the homotopy category of differential graded
`(A, B)`-bimodules to its derived category. -/
@[stacks 09ST "localization functor for DG bimodules"]
abbrev Q (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) :
    CategoryTheory.Functor
      (K R (DifferentialGradedBimodule.{u, v, w, x} A B))
      (Category.{u, v, w, x} A B) :=
  DifferentialGradedModule.Derived.Q.{u, v, max w x}
    (CochainDGAlgebra.enveloping A B)

/-- A differential graded bimodule viewed in the homotopy category of modules over its
enveloping DGA. -/
@[stacks 09ST "homotopy object of a DG bimodule"]
abbrev homotopyObject (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    K R (DifferentialGradedBimodule.{u, v, w, x} A B) :=
  (DifferentialGradedModule.toK (CochainDGAlgebra.enveloping A B)).obj N

/-- A differential graded bimodule viewed in its full bimodule derived category. -/
@[stacks 09ST "derived object of a differential graded bimodule"]
abbrev object (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    Category.{u, v, w, x} A B :=
  (Q A B).obj (homotopyObject N)

/-- The canonical functor from differential graded bimodules to their full bimodule-derived
category. -/
@[stacks 09ST "canonical functor from DG bimodules to the derived category"]
def fromBimodules (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) :
    DifferentialGradedBimodule.{u, v, w, x} A B ⥤
      Category.{u, v, w, x} A B :=
  DifferentialGradedModule.Derived.fromModules.{u, v, max w x}
    (CochainDGAlgebra.enveloping A B)

/-- The canonical functor from differential graded bimodules to their derived category is
additive. -/
@[stacks 09ST "additivity of the canonical functor to the DG bimodule derived category"]
noncomputable instance fromBimodulesAdditive (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) :
    (fromBimodules A B).Additive := sorry

/-- The canonical functor from differential graded bimodules to their derived category is
`R`-linear. -/
@[stacks 09ST "linearity of the canonical functor to the DG bimodule derived category"]
noncomputable instance fromBimodulesLinear (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) :
    Functor.Linear R (fromBimodules A B) := sorry

/-- The canonical bimodule-to-derived functor sends a bimodule to its full derived object. -/
@[simp, stacks 09ST "canonical DG bimodule as a derived object"]
theorem fromBimodules_obj
    (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (fromBimodules A B).obj N = object N := sorry

/-- The bimodule-to-derived functor maps a bimodule morphism through its represented homotopy
class. -/
@[simp, stacks 09ST "morphism map of the canonical DG bimodule derived functor"]
theorem fromBimodules_map
    {N N' : DifferentialGradedBimodule.{u, v, w, x} A B}
    (f : N ⟶ N') :
    (fromBimodules A B).map f =
      (Q A B).map
        ((DifferentialGradedModule.toK (CochainDGAlgebra.enveloping A B)).map f) := sorry

/-- The full bimodule-derived category is the localization of strict bimodules at
quasi-isomorphisms. -/
@[stacks 09ST "DG bimodule derived category as a quasi-isomorphism localization"]
instance fromBimodulesIsLocalization (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) :
    (fromBimodules A B).IsLocalization
      (DifferentialGradedBimodule.quasiIso A B) := sorry

/-- Every derived DG bimodule is represented, up to isomorphism, by a strict DG bimodule. -/
@[stacks 09ST "essential surjectivity of the DG bimodule localization"]
noncomputable instance fromBimodulesEssSurj (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) :
    (fromBimodules A B).EssSurj := sorry

end Derived

/-- The underlying right module of a differential graded bimodule, viewed in the differential
graded homotopy category. -/
@[stacks 09R9 "underlying right-module homotopy object"]
abbrev rightHomotopyObject
    (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    K R (DifferentialGradedModule.{u, v} B) :=
  (DifferentialGradedModule.toK B).obj N.toRightModule

/-- The right module underlying a differential graded bimodule, viewed in the canonical derived
category of the right-hand algebra.  This forgets the left action; use `Derived.object` for the
full bimodule-derived object. -/
@[stacks 09R9 "derived object of a differential graded bimodule", stacks 09S7]
abbrev rightDerivedObject
    (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    DifferentialGradedModule.Derived.Category.{u, v, x} B :=
  (DifferentialGradedModule.Derived.Q B).obj N.rightHomotopyObject

/-- Forgetting the left action and passing to the derived category is functorial in a
differential graded bimodule. -/
@[stacks 09R9 "underlying right derived object as a functor"]
abbrev rightDerivedObjectFunctor (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) :
    DifferentialGradedBimodule.{u, v, w, x} A B ⥤
      DifferentialGradedModule.Derived.Category.{u, v, x} B :=
  DifferentialGradedModule.toK (CochainDGAlgebra.enveloping A B) ⋙
    (CochainDGAlgebra.Enveloping.rightHom A B).restrictDgFunctor.mapK ⋙
      DifferentialGradedModule.Derived.Q B

/-- The functorial underlying right derived object agrees with `rightDerivedObject`. -/
@[stacks 09R9 "underlying right derived object computation", simp]
theorem rightDerivedObjectFunctor_obj
    (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (rightDerivedObjectFunctor A B).obj N = N.rightDerivedObject := sorry

/-- A bimodule morphism acts on underlying right derived objects by localizing its restricted
right-module morphism. -/
@[stacks 09R9 "underlying right derived morphism computation", simp]
theorem rightDerivedObjectFunctor_map
    {N N' : DifferentialGradedBimodule.{u, v, w, x} A B} (f : N ⟶ N') :
    (rightDerivedObjectFunctor A B).map f =
      (DifferentialGradedModule.Derived.Q B).map
        ((DifferentialGradedModule.toK B).map (Hom.toRightHom f)) := sorry

/-- The underlying right derived object functor inverts bimodule quasi-isomorphisms.  This is
the inversion prerequisite for descending constructions from strict bimodules. -/
@[stacks 09R9 "underlying right derived objects invert bimodule quasi-isomorphisms"]
theorem rightDerivedObjectFunctor_map_isIso_of_quasiIso
    {N N' : DifferentialGradedBimodule.{u, v, w, x} A B} (f : N ⟶ N')
    (hf : DifferentialGradedBimodule.quasiIso A B f) :
    IsIso ((rightDerivedObjectFunctor A B).map f) := sorry

/-- The underlying right derived object functor inverts all bimodule
quasi-isomorphisms. -/
@[stacks 09R9 "underlying right derived objects invert bimodule quasi-isomorphisms"]
theorem rightDerivedObjectFunctor_inverts (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) :
    (DifferentialGradedBimodule.quasiIso A B).IsInvertedBy
      (rightDerivedObjectFunctor A B) := sorry

namespace Derived

/-- Restriction to the underlying right module, descended from strict bimodules to the full
bimodule-derived category. -/
@[stacks 09R9 "underlying right module functor on the bimodule-derived category"]
noncomputable abbrev forgetToRightModule (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) :
    Category.{u, v, w, x} A B ⥤
      DifferentialGradedModule.Derived.Category.{u, v, x} B :=
  CochainDGAlgebra.Hom.Derived.restriction
    (CochainDGAlgebra.Enveloping.rightHom A B)

/-- Before localization, derived restriction to the underlying right module recovers the
strict underlying right derived object functor. -/
@[stacks 09R9 "strict factorization of derived restriction to right modules"]
noncomputable def forgetToRightModuleFactors
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) :
    fromBimodules A B ⋙ forgetToRightModule A B ≅
      rightDerivedObjectFunctor A B :=
  Functor.isoWhiskerLeft
    (DifferentialGradedModule.toK (CochainDGAlgebra.enveloping A B))
    (CochainDGAlgebra.Hom.Derived.restrictionFac
      (CochainDGAlgebra.Enveloping.rightHom A B))

/-- Derived restriction to the underlying right module is the canonical localization lift of
strict restriction followed by passage to the derived category. -/
@[stacks 09R9 "localization lift of restriction to underlying right modules"]
noncomputable instance forgetToRightModuleLifting
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) :
    Localization.Lifting (fromBimodules A B)
      (DifferentialGradedBimodule.quasiIso A B)
      (rightDerivedObjectFunctor A B) (forgetToRightModule A B) :=
  ⟨forgetToRightModuleFactors A B⟩

/-- On a strict bimodule, derived restriction recovers its underlying right derived object. -/
@[stacks 09R9 "restriction of a strict bimodule in the derived category"]
noncomputable def forgetToRightModuleObjIso
    (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (forgetToRightModule A B).obj (object N) ≅ N.rightDerivedObject :=
  (forgetToRightModuleFactors A B).app N

/-- On a strict bimodule morphism, derived restriction is conjugate to restriction before
localization by the canonical factorization isomorphism. -/
@[stacks 09R9 "morphism map of derived restriction on strict bimodules"]
theorem forgetToRightModule_map_fromBimodules
    {N N' : DifferentialGradedBimodule.{u, v, w, x} A B} (f : N ⟶ N') :
    (forgetToRightModule A B).map ((fromBimodules A B).map f) =
      (forgetToRightModuleFactors A B).hom.app N ≫
        (rightDerivedObjectFunctor A B).map f ≫
          (forgetToRightModuleFactors A B).inv.app N' := sorry

end Derived

#synth (Derived.fromBimodules A B).Additive
#synth Functor.Linear R (Derived.fromBimodules A B)
#synth (Derived.fromBimodules A B).EssSurj

#synth (rightDerivedObjectFunctor A B).Additive
#synth Functor.Linear R (rightDerivedObjectFunctor A B)

#synth (Derived.forgetToRightModule A B).Additive
#synth Functor.Linear R (Derived.forgetToRightModule A B)

end DifferentialGradedBimodule
