module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Factorization through injective module maps

These statements express range containment as the canonical criterion for factoring one module
map through a monomorphism.  The comap formulation is included for arguments that naturally build
preimage submodules.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace ModuleCat.Factorization

variable {R : Type u} [Ring R]
variable {X Y Z : ModuleCat.{v} R}

/-- The inverse-image submodule of the range of `i` along `f`. It consists of the elements of
`Z` whose image under `f` already lies in the image of `i`. -/
def preimage (i : X ⟶ Y) (f : Z ⟶ Y) : Submodule R Z :=
  Submodule.comap f.hom (LinearMap.range i.hom)

/-- Membership in `preimage i f` means that the image under `f` lies in the range of `i`. -/
@[simp]
theorem mem_preimage_iff (i : X ⟶ Y) (f : Z ⟶ Y) (z : Z) :
    z ∈ preimage i f ↔ f.hom z ∈ LinearMap.range i.hom := sorry

/-- A module map whose range is contained in the range of a monomorphism factors through that
monomorphism. -/
theorem exists_of_range_le (i : X ⟶ Y) [Mono i] (f : Z ⟶ Y)
    (h : LinearMap.range f.hom ≤ LinearMap.range i.hom) :
    ∃ g : Z ⟶ X, g ≫ i = f := sorry

/-- A map factors through a monomorphism if every source element belongs to its range
preimage. -/
theorem exists_of_preimage_eq_top (i : X ⟶ Y) [Mono i] (f : Z ⟶ Y)
    (h : preimage i f = ⊤) :
    ∃ g : Z ⟶ X, g ≫ i = f := sorry

end ModuleCat.Factorization
