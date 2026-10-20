module

public import ReasLib.CategoryTheory.Filtration.Morphism.PageRepresentatives
public import ReasLib.CategoryTheory.Filtration.ZeroMorphisms
public import ReasLib.Algebra.Module.Submodule.Filtration
public import Mathlib.Algebra.Homology.HomologicalComplex
import StacksCheckRecall

@[expose] public section
open CategoryTheory CategoryTheory.Limits

universe v u uR uM
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
variable (p : ℤ)

namespace StacksEquation012H

/-- The displayed union lies in the intrinsic image representative whenever that union exists. -/
theorem union_le_image (B : Subobject (K.X PUnit.unit).obj)
    (hB : IsLUB (Set.range fun r : ℕ ↦
      FilteredObject.Hom.boundaryRepresentative (K.d PUnit.unit PUnit.unit) r p) B) :
    B ≤ FilteredObject.Hom.imageRepresentative (K.d PUnit.unit PUnit.unit) p := by
  apply hB.2
  rintro _ ⟨r, rfl⟩
  apply sup_le_sup_right
  apply le_inf
  · exact le_trans inf_le_right (imageSubobject_comp_le _ _)
  · exact inf_le_left

end StacksEquation012H

/- 12.23.5.2: the source's union is its least upper bound of the increasing finite-page
representatives. Existence of that bound suffices; no complete lattice is added here. -/
@[stacks 012H] #check
  (StacksEquation012H.union_le_image K p :
    ∀ (B : Subobject (K.X PUnit.unit).obj),
      IsLUB (Set.range fun r : ℕ ↦
        ((K.X PUnit.unit).filtration.stage p ⊓
          imageSubobject (((K.X PUnit.unit).filtration.stage (p - r + 1)).arrow ≫
            (K.d PUnit.unit PUnit.unit).hom)) ⊔
              (K.X PUnit.unit).filtration.stage (p + 1)) B →
      B ≤ (imageSubobject (K.d PUnit.unit PUnit.unit).hom ⊓ (K.X PUnit.unit).filtration.stage p) ⊔
        (K.X PUnit.unit).filtration.stage (p + 1))

variable [LocallySmall.{v} C] [WellPowered.{v} C] [HasCoproducts.{v} C]

/- 12.23.5.2: the supremum of the finite-page boundary representatives is contained
in the intrinsic image representative, retaining the filtration-negligible summand. -/
#check
  (FilteredObject.Hom.Representative.Boundary.eventual_le_image
      (K.d PUnit.unit PUnit.unit) p :
    Subobject.sSup.{v} (Set.range fun r : ℕ ↦ ((K.X PUnit.unit).filtration.stage p ⊓
      imageSubobject (((K.X PUnit.unit).filtration.stage (p - r + 1)).arrow ≫
        (K.d PUnit.unit PUnit.unit).hom)) ⊔ (K.X PUnit.unit).filtration.stage (p + 1)) ≤
    (imageSubobject (K.d PUnit.unit PUnit.unit).hom ⊓ (K.X PUnit.unit).filtration.stage p) ⊔
      (K.X PUnit.unit).filtration.stage (p + 1))

section Module
variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable (d : M →ₗ[R] M) (F : ℤ → Submodule R M)

/- The same containment, expanded into the submodule operations used in module calculations. -/
#check (Submodule.FilteredLinearMap.Representative.Boundary.eventual_le_range d F F p :
  (⨆ r : ℕ, (F p ⊓ Submodule.map d (F (p - r + 1))) ⊔ F (p + 1)) ≤
    (LinearMap.range d ⊓ F p) ⊔ F (p + 1))
end Module
