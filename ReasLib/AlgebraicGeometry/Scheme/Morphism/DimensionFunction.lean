module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFormula
public import ReasLib.Topology.Specialization.Dimension

/-!
# Dimension functions induced by scheme morphisms

This file defines the dimension function obtained by adding residue-field transcendence degree
to a dimension function on the target of a scheme morphism.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The relative dimension function associated to `f : X ⟶ S` and `δ : S → ℤ` sends a point
`x` to `δ (f x)` plus the transcendence degree of `κ(x)` over `κ(f(x))`. -/
noncomputable abbrev relativeDimensionFunction
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (δ : S → ℤ) : X → ℤ :=
  fun x ↦ δ (f x) + ((f.residueFieldTranscendenceDegreeAt x).toNat : ℤ)

/-- Equal locally finite type maps induce equal relative dimension functions. -/
theorem relativeDimensionFunction_congr {X S : Scheme.{u}}
    {f g : X ⟶ S} [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (h : f = g) (δ : S → ℤ) :
    f.relativeDimensionFunction δ = g.relativeDimensionFunction δ := by
  subst g
  rfl

/-- A locally finite-type morphism to a universally catenary scheme pulls a dimension function
on the target back to a dimension function after adding residue-field transcendence degree. -/
instance instIsDimensionFunctionRelativeDimensionFunction
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] :
    IsDimensionFunction (f.relativeDimensionFunction δ) := sorry

end AlgebraicGeometry.Scheme.Hom
