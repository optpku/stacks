module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Homotopy

/-!
# Additive and Linear Structure on DG Homotopy Categories

This leaf promotes the homotopy-class modules from `DifferentialGraded/Homotopy`
to the categorical `Preadditive` and `Linear` structures on `K`.  It also records
that the quotient functor from closed degree-zero morphisms preserves both structures.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {C : Type v}
variable [D : DifferentialGradedCategory R C]

open scoped DifferentialGradedCategory

/-- The additive commutative group on a hom-space of the DG homotopy category. -/
@[stacks 09JQ "additive hom groups of the DG homotopy category"]
instance kHomAddCommGroup (X Y : K R C) : AddCommGroup (X ⟶ Y) :=
  inferInstanceAs <| AddCommGroup (HomotopyClass X.obj Y.obj)

/-- The canonical `R`-module structure on a hom-space of the DG homotopy category. -/
@[stacks 09JQ "module structure on DG homotopy classes"]
instance kHomModule (X Y : K R C) : Module R (X ⟶ Y) :=
  inferInstanceAs <| Module R (HomotopyClass X.obj Y.obj)

/-- Addition is compatible with postcomposition in the DG homotopy category. -/
@[stacks 09JQ "postcomposition and addition in the DG homotopy category"]
theorem kPreadditive_add_comp (X Y Z : K R C) (f f' : X ⟶ Y) (g : Y ⟶ Z) :
    (f + f') ≫ g = f ≫ g + f' ≫ g := sorry

/-- Addition is compatible with precomposition in the DG homotopy category. -/
@[stacks 09JQ "precomposition and addition in the DG homotopy category"]
theorem kPreadditive_comp_add (X Y Z : K R C) (f : X ⟶ Y) (g g' : Y ⟶ Z) :
    f ≫ (g + g') = f ≫ g + f ≫ g' := sorry

/-- The DG homotopy category is canonically preadditive. -/
@[stacks 09JQ "preadditive structure on the DG homotopy category"]
instance kPreadditive : Preadditive (K R C) where
  homGroup X Y := kHomAddCommGroup X Y
  add_comp X Y Z f f' g := kPreadditive_add_comp X Y Z f f' g
  comp_add X Y Z f g g' := kPreadditive_comp_add X Y Z f g g'

/-- Scalar multiplication is compatible with postcomposition in the DG homotopy category. -/
@[stacks 09JQ "postcomposition and scalar multiplication in the DG homotopy category"]
theorem kLinear_smul_comp (X Y Z : K R C) (r : R)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (r • f) ≫ g = r • (f ≫ g) := sorry

/-- Scalar multiplication is compatible with precomposition in the DG homotopy category. -/
@[stacks 09JQ "precomposition and scalar multiplication in the DG homotopy category"]
theorem kLinear_comp_smul (X Y Z : K R C)
    (f : X ⟶ Y) (r : R) (g : Y ⟶ Z) :
    f ≫ (r • g) = r • (f ≫ g) := sorry

/-- The explicit `R`-linear structure on the DG homotopy category. -/
@[reducible]
def kLinearData : Linear R (K R C) where
  homModule X Y := kHomModule X Y
  smul_comp := kLinear_smul_comp
  comp_smul := kLinear_comp_smul

/-- The DG homotopy category is canonically `R`-linear. -/
@[stacks 09JQ "linear structure on the DG homotopy category"]
instance kLinear : Linear R (K R C) := kLinearData

/-- Explicit access to the canonical linear structure on the DG homotopy category. -/
abbrev linearStructure : Linear R (K R C) := kLinearData

namespace Comp

/-- The quotient functor to the DG homotopy category preserves addition of closed morphisms. -/
@[simp, stacks 09JQ "additivity of the DG homotopy quotient on morphisms"]
theorem inKFunctor_map_add {X Y : Comp R C} (f g : X ⟶ Y) :
    (inKFunctor : Comp R C ⥤ K R C).map (f + g) =
      (inKFunctor : Comp R C ⥤ K R C).map f + (inKFunctor : Comp R C ⥤ K R C).map g := sorry

/-- The quotient functor to the DG homotopy category preserves scalar multiplication. -/
@[simp, stacks 09JQ "linearity of the DG homotopy quotient on morphisms"]
theorem inKFunctor_map_smul {X Y : Comp R C} (r : R) (f : X ⟶ Y) :
    (inKFunctor : Comp R C ⥤ K R C).map (r • f) =
      r • (inKFunctor : Comp R C ⥤ K R C).map f := sorry

/-- The quotient functor to the DG homotopy category is additive. -/
@[stacks 09JQ "additive DG homotopy quotient functor"]
def inKFunctor_additive :
    (inKFunctor : Comp R C ⥤ K R C).Additive where
  map_add := fun {X Y} f g ↦
    inKFunctor_map_add (R := R) (C := C) (X := X) (Y := Y) f g

/-- The quotient functor to the DG homotopy category is `R`-linear. -/
@[stacks 09JQ "linear DG homotopy quotient functor"]
def inKFunctor_linear : Functor.Linear R (inKFunctor : Comp R C ⥤ K R C) where
  map_smul := fun {X Y} f r ↦
    inKFunctor_map_smul (R := R) (C := C) (X := X) (Y := Y) r f

end Comp

end DifferentialGradedCategory
