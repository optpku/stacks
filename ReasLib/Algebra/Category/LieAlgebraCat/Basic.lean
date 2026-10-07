module

public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Lie.Basic

/-!
# The category of Lie algebras

This file bundles Lie algebras over a fixed commutative ring as a concrete category and provides
the forgetful functor to modules.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

variable (R : Type u) [CommRing R]

/-- The bundled category of Lie algebras over a fixed commutative ring. -/
structure LieAlgebraCat where
  /-- The underlying carrier type. -/
  carrier : Type v
  /-- The Lie-ring structure on the carrier. -/
  [instLieRing : LieRing carrier]
  /-- The Lie-algebra structure over the base ring. -/
  [instLieAlgebra : LieAlgebra R carrier]

attribute [instance] LieAlgebraCat.instLieRing LieAlgebraCat.instLieAlgebra

namespace LieAlgebraCat

/-- A bundled Lie algebra coerces to its underlying carrier type. -/
instance : CoeSort (LieAlgebraCat R) (Type v) :=
  ⟨LieAlgebraCat.carrier⟩

/-- The object in the category of Lie algebras associated to a type equipped with the appropriate
typeclasses. -/
abbrev of (L : Type v) [LieRing L] [LieAlgebra R L] : LieAlgebraCat R :=
  ⟨L⟩

/-- Lie algebras over `R` form a category with Lie algebra homomorphisms as morphisms. -/
instance : Category (LieAlgebraCat R) where
  Hom L M := L →ₗ⁅R⁆ M
  id L := LieHom.id
  comp f g := LieHom.comp g f

/-- The category of Lie algebras over `R` is concrete over its carrier types. -/
instance : ConcreteCategory (LieAlgebraCat R) (· →ₗ⁅R⁆ ·) where
  hom := fun f ↦ f
  ofHom := fun f ↦ f
  hom_ofHom := fun _ ↦ rfl
  ofHom_hom := fun _ ↦ rfl
  id_apply := fun _ ↦ rfl
  comp_apply := fun _ _ _ ↦ rfl

/-- Typecheck a Lie algebra morphism as a categorical morphism. -/
abbrev ofHom {L M : Type v} [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]
    (f : L →ₗ⁅R⁆ M) : of R L ⟶ of R M :=
  f

/-- Two morphisms of bundled Lie algebras are equal when they agree on every element. -/
@[ext]
lemma hom_ext {L M : LieAlgebraCat R} {f g : L ⟶ M} (h : ∀ x, f x = g x) : f = g :=
  LieHom.ext fun x ↦ h x

/-- The underlying `R`-module of a bundled Lie algebra. -/
abbrev toModuleCat (L : LieAlgebraCat R) : ModuleCat R :=
  ModuleCat.of R L

/-- Forgetting the Lie bracket gives the underlying `R`-module functor. -/
instance : HasForget₂ (LieAlgebraCat R) (ModuleCat R) where
  forget₂ :=
    { obj := toModuleCat (R := R)
      map := fun f ↦ ModuleCat.ofHom f.toLinearMap }
  forget_comp := rfl

/-- On morphisms, the forgetful functor to `ModuleCat R` uses the underlying linear map. -/
@[simp]
lemma forget₂_module_map {L M : LieAlgebraCat R} (f : L ⟶ M) :
    (forget₂ (LieAlgebraCat R) (ModuleCat R)).map f = ModuleCat.ofHom f.toLinearMap :=
  rfl

end LieAlgebraCat
