/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Dimension.Stalk

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField

/-!
# Dimension formula for scheme morphisms

This file records local and global dimension formulas for scheme morphisms.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Hom

namespace DimensionFormula

/-- The supremum of the residue-field transcendence degrees at the generic points of the
irreducible components of the source of a locally finite-type morphism. -/
noncomputable def genericComponentTrdeg
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] : ℕ∞ :=
  ⨆ Z : irreducibleComponents X,
    (f.residueFieldTrdegAt (genericPoints.ofComponent Z) : ℕ∞)

/-- For a locally finite-type morphism to a locally Noetherian scheme, the Krull dimension of
the source stalk plus the residue-field transcendence degree is bounded by the Krull dimension
of the target stalk plus the greatest generic-component transcendence degree through the source
point. -/
theorem stalk_add_trdeg_le_genericMax
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S]
    (x : X) (E : ℕ)
    (hE :
      IsGreatest
        {n : ℕ |
          ∃ Z : irreducibleComponents X,
            x ∈ (Z : Set X) ∧
              n = f.residueFieldTrdegAt (genericPoints.ofComponent Z)} E) :
    ringKrullDim (X.presheaf.stalk x) + f.residueFieldTrdegAt x ≤
      ringKrullDim (S.presheaf.stalk (f x)) + E := sorry

/-- For a dominant locally finite-type morphism of integral schemes with locally Noetherian
target, the source-stalk dimension plus the residue-field transcendence degree is bounded by
the target-stalk dimension plus the induced function-field transcendence degree. -/
theorem stalk_add_trdeg_le_functionFieldTrdeg
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S]
    [IsIntegral X] [IsIntegral S] [IsDominant f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) + f.residueFieldTrdegAt x ≤
      ringKrullDim (S.presheaf.stalk (f x)) +
        f.functionFieldTrdeg f.map_genericPoint_eq_of_isDominant := sorry

/-- For a dominant locally finite-type morphism of integral schemes with universally catenary
target, the source-stalk dimension plus the residue-field transcendence degree equals the
target-stalk dimension plus the induced function-field transcendence degree. -/
theorem stalk_add_trdeg_eq_functionFieldTrdeg_of_universallyCatenary
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [UniversallyCatenary S]
    [IsIntegral X] [IsIntegral S] [IsDominant f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) + f.residueFieldTrdegAt x =
      ringKrullDim (S.presheaf.stalk (f x)) +
        f.functionFieldTrdeg f.map_genericPoint_eq_of_isDominant := sorry

/-- For a flat morphism of locally Noetherian schemes having relative dimension `d`, the local
topological Krull dimension at a source point is the local dimension at its image plus `d`. -/
theorem topologicalKrullDimAt_eq_image_add_relativeDimension_of_flat
    {X Y : Scheme.{u}} {d : ℕ} (f : X ⟶ Y) [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [Flat f] [RelativeDimension f d] (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (f x) + (d : WithBot ℕ∞) := sorry

/-- The topological Krull dimension of the source of a locally finite-type morphism to a
locally Noetherian scheme is at most the dimension of the target plus the supremum of the
generic-component residue-field transcendence degrees. -/
theorem topologicalKrullDim_le_add_genericComponentTrdeg
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y] :
    topologicalKrullDim X ≤
      topologicalKrullDim Y + (genericComponentTrdeg f : WithBot ℕ∞) := sorry

/-- For a dominant locally finite-type morphism of integral schemes with locally Noetherian
target, the topological Krull dimension of the source is bounded by the dimension of the target
plus the transcendence degree of the induced extension of function fields. -/
theorem topologicalKrullDim_le_add_functionFieldTrdeg
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    topologicalKrullDim X ≤
      topologicalKrullDim Y +
        (f.functionFieldTrdeg f.map_genericPoint_eq_of_isDominant : WithBot ℕ∞) := sorry

/-- For a dominant locally finite-type morphism of integral schemes with locally Noetherian
target whose underlying map is closed, the topological Krull dimension of the source is the
dimension of the target plus the transcendence degree of the induced extension of function
fields. -/
theorem topologicalKrullDim_eq_add_functionFieldTrdeg_of_isClosedMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    [IsIntegral X] [IsIntegral Y] [IsDominant f] (hclosed : IsClosedMap f.base) :
    topologicalKrullDim X =
      topologicalKrullDim Y +
        (f.functionFieldTrdeg f.map_genericPoint_eq_of_isDominant : WithBot ℕ∞) := sorry

end DimensionFormula

end AlgebraicGeometry.Scheme.Hom
