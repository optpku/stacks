module

public import ReasLib.AlgebraicGeometry.Scheme.Distance
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension

/-!
# Distance under finite-type morphisms
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The distance to the inverse image of a closed subset under a finite-type morphism. -/
noncomputable def distanceToPreimage {Y Y' : Scheme.{u}} [IsNoetherian Y]
    (f : Y' ⟶ Y) [Hom.FiniteType f] (Z : Closeds Y) : Y' → ℕ∞ :=
  @AlgebraicGeometry.Scheme.distanceTo Y' (Hom.FiniteType.isNoetherian f)
    (Z.preimage f.continuous)

/-- The preimage distance agrees with the distance function on the source scheme when its
Noetherian structure is available directly. -/
theorem distanceToPreimage_eq {Y Y' : Scheme.{u}} [IsNoetherian Y] (f : Y' ⟶ Y)
    [Hom.FiniteType f] [IsNoetherian Y'] (Z : Closeds Y) (y' : Y') :
    f.distanceToPreimage Z y' = Y'.distanceTo (Z.preimage f.continuous) y' := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

/-- Distance to a closed subset does not increase by more than the fibre dimension under a
finite-type morphism, after subtracting the residue-field transcendence degree. -/
theorem distanceTo_preimage_le {Y Y' : Scheme.{u}} [IsNoetherian Y] [UniversallyCatenary Y]
    (Z : Closeds Y) (f : Y' ⟶ Y) [Hom.FiniteType f] (e : ℕ)
    (h_fibers : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (e : WithBot ℕ∞)) (y' : Y') :
    Y.distanceTo Z (f y') ≤ f.distanceToPreimage Z y' + e - f.residueFieldTrdegAt y' := sorry

end AlgebraicGeometry.Scheme
