/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.SetTheory.Ordinal.Univ
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cardinality of complexes of sheaves of modules

The cardinality used here counts all sections in all cochain degrees.  The derived-object
cardinal is the infimum of these cardinals over all representatives.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe u v w z

namespace SheafOfModules.CochainComplex

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})

/-- The cardinality of all objectwise sections in all degrees of a cochain complex of module
sheaves. -/
@[stacks 0GYZ "cardinality of a module-sheaf complex"]
def sectionsCardinal
    (F : _root_.CochainComplex (SheafOfModules.{z} R) ℤ) :
    Cardinal.{max (max u v) (max w z)} :=
  Cardinal.lift.{max (max u v) (max w z), max u z}
    (Cardinal.mk (Σ i : ℤ, Σ U : C, (F.X i).val.obj (op U)))

/- The section-cardinality of an object in the canonical source of the derived localization.
The local preadditive pin below makes its cochain-complex presentation definitionally agree with
`DerivedCategory.Q`; it carries no additional mathematical choice. -/
section Derived

variable [hA : Abelian (SheafOfModules.{z} R)]
variable [HasDerivedCategory (SheafOfModules.{z} R)]

/-- The preadditive structure selected by the abelian structure used by `DerivedCategory.Q`. -/
local instance derivedPreadditive : Preadditive (SheafOfModules.{z} R) := hA.toPreadditive

/-- The section-cardinality of a representative in the derived localization model. -/
def representativeSectionsCardinal
    (F : _root_.CochainComplex (SheafOfModules.{z} R) ℤ) :
    Cardinal.{max (max u v) (max w z)} :=
  Cardinal.lift.{max (max u v) (max w z), max u z}
    (Cardinal.mk (Σ i : ℤ, Σ U : C, (F.X i).val.obj (op U)))

/-- The least section-cardinality among cochain complexes representing a derived module
sheaf. -/
@[stacks 0GYZ "cardinality of a derived module sheaf"]
def derivedObjectCardinal (K : DerivedCategory (SheafOfModules.{z} R)) :
    Cardinal.{max (max u v) (max w z)} :=
  sInf {kappa : Cardinal.{max (max u v) (max w z)} |
    ∃ (F : _root_.CochainComplex (SheafOfModules.{z} R) ℤ)
      (_ : DerivedCategory.Q.obj F ≅ K), representativeSectionsCardinal R F ≤ kappa}

/-- Every chosen representative bounds the least section-cardinality from above. -/
theorem derivedObjectCardinal_le_of_representation
    {K : DerivedCategory (SheafOfModules.{z} R)}
    (F : _root_.CochainComplex (SheafOfModules.{z} R) ℤ)
    (e : DerivedCategory.Q.obj F ≅ K) :
    derivedObjectCardinal R K ≤ representativeSectionsCardinal R F := sorry

end Derived

end SheafOfModules.CochainComplex
