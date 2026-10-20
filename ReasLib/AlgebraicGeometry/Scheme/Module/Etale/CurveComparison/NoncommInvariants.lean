module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommDualResolution
public import Mathlib.CategoryTheory.Abelian.RightDerived

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
noncomputable section
universe u v

namespace NoncommInvariants
variable (R : Type u) [Ring R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Fixed vectors form a LEFT R-submodule even for noncommutative R. -/
def submodule (M : DiscreteModuleCat R G) : Submodule R M.obj.V where
  carrier := {m | ∀ g : G, (M.obj.ρ g).hom m = m}
  zero_mem' := by intro g; exact map_zero _
  add_mem' := by intro x y hx hy g; simp [map_add, hx g, hy g]
  smul_mem' := by intro r x hx g; simp [map_smul, hx g]

/-- Actual coefficient maps restricted to invariant vectors. -/
def map {M N : DiscreteModuleCat R G} (f : M ⟶ N) :
    submodule R G M →ₗ[R] submodule R G N :=
  LinearMap.codRestrict (submodule R G N)
    (f.hom.hom.hom.domRestrict (submodule R G M)) (by sorry)

/-- Continuous invariants on ALL discrete representations, before finite input inclusion. -/
def functor : DiscreteModuleCat R G ⥤ ModuleCat.{max u v} R where
  obj M := ModuleCat.of R (submodule R G M)
  map f := ModuleCat.ofHom (map R G f)
  map_id := by intros; rfl
  map_comp := by intros; rfl

instance functor_additive : (functor R G).Additive where
  map_add := by intros; rfl

/-- Derived continuous invariants use the actual ambient injective resolutions. -/
def cohomology (n : ℕ) := (functor R G).rightDerived n

end NoncommInvariants
