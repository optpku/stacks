module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Length
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.FittingIdeal
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Union
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField.Separable
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RamificationIndex
public import ReasLib.AlgebraicGeometry.Scheme.OverField.ClosedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.FieldRamification

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Curve

variable {k : Type u} [Field k]

/-- The natural-valued multiplicity of the Kähler different at a closed point of a curve. -/
noncomputable def kaehlerDifferentMultiplicity
    {X Y : SchemeOverField k} (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (x : closedPoints X.left) : ℕ :=
  (Module.length (stalkRing X x.1)
    (RingedSpace.stalkModuleCat
      (closedSubschemeStructureSheafOn (kaehlerDifferent f.left)) x.1)).toNat

/-- The Kähler-different multiplicity is the natural number underlying the ambient stalk length
of the closed-subscheme structure sheaf. -/
theorem kaehlerDifferentMultiplicity_def
    {X Y : SchemeOverField k} (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (x : closedPoints X.left) :
    kaehlerDifferentMultiplicity f x =
      (Module.length (stalkRing X x.1)
        (RingedSpace.stalkModuleCat
          (closedSubschemeStructureSheafOn (kaehlerDifferent f.left)) x.1)).toNat := sorry

/-- For a finite separable morphism of smooth proper curves with constant global functions, the
multiplicity of the Kähler different equals the length of the relative differential stalk. -/
theorem kaehlerDifferentMultiplicity_eq_relativeDifferentialsLength
    {X Y : SchemeOverField k} [Curve X] [Curve Y] [IsProper X.hom] [IsProper Y.hom]
    [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    [LocallyOfFiniteType f.left] [IsDominant f.left]
    (h_finite : f.left.FiniteFunctionFieldExtension)
    (h_separable : f.left.SeparableFunctionFieldExtension)
    (hΓX : Function.Bijective (globalSectionsMap X.hom))
    (hΓY : Function.Bijective (globalSectionsMap Y.hom)) (x : closedPoints X.left) :
    (kaehlerDifferentMultiplicity f x : ℕ∞) =
      Module.length (stalkRing X x.1)
        (RingedSpace.stalkModuleCat (Ω[f.left.toShHom]) x.1) := sorry

/-- For a finite separable morphism of smooth proper curves, the Kähler-different multiplicity at a
closed point is at least the ramification index minus one. -/
theorem ramificationIndexAt_sub_one_le_multiplicity
    {X Y : SchemeOverField k} [Curve X] [Curve Y] [IsProper X.hom] [IsProper Y.hom]
    [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    [LocallyOfFiniteType f.left] [IsDominant f.left]
    (h_finite : f.left.FiniteFunctionFieldExtension)
    (h_separable : f.left.SeparableFunctionFieldExtension)
    (hΓX : Function.Bijective (globalSectionsMap X.hom))
    (hΓY : Function.Bijective (globalSectionsMap Y.hom)) (x : closedPoints X.left) :
    kaehlerDifferentMultiplicity f x ≥ f.left.ramificationIndexAt x.1 - 1 := sorry

/-- For a finite separable morphism of smooth proper curves, equality in the ramification bound at a
closed point is equivalent to separable residue extension and tame ramification index. -/
theorem multiplicity_eq_ramificationIndexAt_sub_one_iff_tame
    {X Y : SchemeOverField k} [Curve X] [Curve Y] [IsProper X.hom] [IsProper Y.hom]
    [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    [LocallyOfFiniteType f.left] [IsDominant f.left]
    (h_finite : f.left.FiniteFunctionFieldExtension)
    (h_separable : f.left.SeparableFunctionFieldExtension)
    (hΓX : Function.Bijective (globalSectionsMap X.hom))
    (hΓY : Function.Bijective (globalSectionsMap Y.hom)) (x : closedPoints X.left) :
    (kaehlerDifferentMultiplicity f x = f.left.ramificationIndexAt x.1 - 1) ↔
      (Algebra.IsSeparable (Y.left.residueField (f.left x.1))
          (X.left.residueField x.1) ∧
        DVR.Field.PrimeToChar (Y.left.residueField (f.left x.1))
          (f.left.ramificationIndexAt x.1)) := sorry

end AlgebraicGeometry.Curve
