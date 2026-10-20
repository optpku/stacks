/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.ToUnbounded

/-!
# Bounded-below affine derived quasicoherent modules

This module restricts the affine derived global-sections equivalence to bounded-below
complexes with quasicoherent cohomology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open DerivedCategory.TStructure
open DerivedCategory.Plus.CohomologyIn
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Affine derived global sections preserve bounded-below objects with quasi-coherent
cohomology. -/
theorem affineGlobalSectionsPlus_boundedBelow (A : CommRingCat.{u}) :
    ∀ K : Plus (Spec A),
      (t.plus : ObjectProperty (DerivedCategory (ModuleCat A)))
        (((toUnbounded
          (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace) ⋙
            affineGlobalSections A).obj K)) := sorry

/-- Affine derived global sections restricted to bounded-below complexes. -/
noncomputable def affineGlobalSectionsPlus (A : CommRingCat.{u}) :
    Plus (Spec A) ⥤ DerivedCategory.Plus (ModuleCat A) :=
  (t.plus : ObjectProperty (DerivedCategory (ModuleCat A))).lift
    (toUnbounded
      (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace) ⋙
        affineGlobalSections A)
    (affineGlobalSectionsPlus_boundedBelow A)

/-- Bounded-below affine derived global sections remain an equivalence. -/
noncomputable instance affineGlobalSectionsPlus_isEquivalence (A : CommRingCat.{u}) :
    Functor.IsEquivalence (affineGlobalSectionsPlus A) := sorry

/-- The bounded-below affine derived associated-sheaf functor. -/
noncomputable def affineTildePlus (A : CommRingCat.{u}) :
    DerivedCategory.Plus (ModuleCat A) ⥤ Plus (Spec A) :=
  Functor.inv (affineGlobalSectionsPlus A)

/-- The bounded-below affine derived associated-sheaf functor is inverse to affine derived
global sections. -/
theorem affineTildePlus_comp_affineGlobalSectionsPlus_isomorphic (A : CommRingCat.{u}) :
    IsIsomorphic (affineTildePlus A ⋙ affineGlobalSectionsPlus A)
      (𝟭 (DerivedCategory.Plus (ModuleCat A))) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
