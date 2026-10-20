/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.ToUnbounded

/-!
# Bounded-below derived coextension on affine schemes

This module restricts derived coextension of scalars along a pseudo-coherent affine
morphism to bounded-below derived categories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open DerivedCategory.TStructure
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Derived coextension of scalars along a pseudo-coherent affine morphism preserves
bounded-below complexes. -/
theorem derivedCoextensionPlus_boundedBelow {A B : CommRingCat.{u}} (f : A ⟶ B)
    [PseudoCoherent (Spec.map f)] :
    ∀ K : DerivedCategory.Plus (ModuleCat A),
      (t.plus : ObjectProperty (DerivedCategory (ModuleCat B)))
        ((((DerivedCategory.Plus.ι :
            DerivedCategory.Plus (ModuleCat A) ⥤ DerivedCategory (ModuleCat A)) ⋙
          ModuleCat.derivedCoextensionOfScalars f.hom).obj K)) := sorry

/-- Derived coextension of scalars, representing `RHom_A(B, -)`, restricted to
bounded-below complexes. -/
noncomputable def derivedCoextensionPlus {A B : CommRingCat.{u}} (f : A ⟶ B)
    [PseudoCoherent (Spec.map f)] :
    DerivedCategory.Plus (ModuleCat A) ⥤ DerivedCategory.Plus (ModuleCat B) :=
  (t.plus : ObjectProperty (DerivedCategory (ModuleCat B))).lift
    ((DerivedCategory.Plus.ι :
        DerivedCategory.Plus (ModuleCat A) ⥤ DerivedCategory (ModuleCat A)) ⋙
      ModuleCat.derivedCoextensionOfScalars f.hom)
    (derivedCoextensionPlus_boundedBelow f)

/-- Forgetting boundedness identifies `derivedCoextensionPlus f` with ordinary derived
coextension of scalars. -/
theorem derivedCoextensionPlus_comp_inclusion_isomorphic
    {A B : CommRingCat.{u}} (f : A ⟶ B) [PseudoCoherent (Spec.map f)] :
    IsIsomorphic
      (derivedCoextensionPlus f ⋙ (DerivedCategory.Plus.ι :
        DerivedCategory.Plus (ModuleCat B) ⥤ DerivedCategory (ModuleCat B)))
      ((DerivedCategory.Plus.ι :
          DerivedCategory.Plus (ModuleCat A) ⥤ DerivedCategory (ModuleCat A)) ⋙
        ModuleCat.derivedCoextensionOfScalars f.hom) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
