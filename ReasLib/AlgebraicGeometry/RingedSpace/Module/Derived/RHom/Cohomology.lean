/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.RHom.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Open cohomology of derived internal Hom on ringed spaces

Degree-zero open cohomology of a derived internal Hom computes morphisms after canonical derived
restriction to the open subspace.  Companion statements transport the target to the chosen-complex
representatives used by source-facing notation.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open CategoryTheory.MonoidalClosed
open scoped CartesianClosed

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.RHom.Cohomology

variable {X Y : RingedSpace.{u}}

/-- Stacks 08DK: degree-zero open cohomology of a derived internal Hom computes morphisms between
the canonical derived restrictions. -/
@[stacks 08DK "open derived internal-Hom cohomology"]
theorem openH0_isomorphic_restrictionHom
    [MonoidalCategory (ModuleDerived X)] [MonoidalClosed (ModuleDerived X)]
    (U : Opens X.carrier) (K L : ModuleDerived X) :
    IsIsomorphic
      ((AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (moduleOpenHypercohomology X U (K ⟹ L) 0))
      (AddCommGrpCat.of
        ((moduleRestrictionToOpenDerived X U).obj K ⟶
          (moduleRestrictionToOpenDerived X U).obj L)) := sorry

/-- Source-facing companion to `openH0_isomorphic_restrictionHom`, with the restricted derived
objects represented by restrictions of chosen cochain-complex preimages. -/
@[stacks 08DK "open internal-Hom cohomology for restricted representatives"]
theorem openH0_isomorphic_representativeHom
    [MonoidalCategory (ModuleDerived X)] [MonoidalClosed (ModuleDerived X)]
    (U : Opens X.carrier) (K L : ModuleDerived X) :
    IsIsomorphic
      ((AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (moduleOpenHypercohomology X U (K ⟹ L) 0))
      (AddCommGrpCat.of
        (restrictedModuleDerivedOnOpen X U K ⟶ restrictedModuleDerivedOnOpen X U L)) := sorry

/-- Evaluation of the degree-zero preimage internal-Hom presheaf over `V` computes morphisms
between the canonical derived restrictions to `f ⁻¹' V`. -/
@[stacks 0D66 "preimage internal-Hom presheaf over an open"]
theorem preimageH0_isomorphic_restrictionHom
    [MonoidalCategory (ModuleDerived X)] [MonoidalClosed (ModuleDerived X)]
    (f : X ⟶ Y) (K L : ModuleDerived X) (V : Opens Y.carrier) :
    IsIsomorphic
      ((AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        ((Pushforward.Cohomology.preimagePresheaf f (K ⟹ L) 0).obj (op V)))
      (AddCommGrpCat.of
        ((moduleRestrictionToOpenDerived X (preimageOpen f V)).obj K ⟶
          (moduleRestrictionToOpenDerived X (preimageOpen f V)).obj L)) := sorry

/-- Source-facing companion to `preimageH0_isomorphic_restrictionHom`, using chosen restricted
representatives. -/
@[stacks 0D66 "preimage internal-Hom presheaf for restricted representatives"]
theorem preimageH0_isomorphic_representativeHom
    [MonoidalCategory (ModuleDerived X)] [MonoidalClosed (ModuleDerived X)]
    (f : X ⟶ Y) (K L : ModuleDerived X) (V : Opens Y.carrier) :
    IsIsomorphic
      ((AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        ((Pushforward.Cohomology.preimagePresheaf f (K ⟹ L) 0).obj (op V)))
      (AddCommGrpCat.of
        (restrictedModuleDerivedOnOpen X (preimageOpen f V) K ⟶
          restrictedModuleDerivedOnOpen X (preimageOpen f V) L)) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.RHom.Cohomology

end
