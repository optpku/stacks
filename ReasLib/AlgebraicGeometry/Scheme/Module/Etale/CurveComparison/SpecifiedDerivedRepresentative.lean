/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v w

namespace SpecifiedDerivedRepresentative
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable (K L : CochainComplex C ℤ) [L.IsKInjective]
variable (f : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L)

/-- The normalized homotopy-category arrow represents THIS specified derived
map. The only inverse is Mathlib's bijection for a K-injective target. -/
def homotopyMap : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L :=
  (Equiv.ofBijective _ (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) L)).symm
      ((DerivedCategory.quotientCompQhIso C).hom.app K ≫ f ≫
        (DerivedCategory.quotientCompQhIso C).inv.app L)

/-- Choose a cochain representative of that fixed homotopy class through the
actual full homotopy quotient. No desired comparison is postulated to exist. -/
def map : K ⟶ L :=
  (HomotopyCategory.quotient C (ComplexShape.up ℤ)).preimage (homotopyMap K L f)

theorem homotopyMap_spec : DerivedCategory.Qh.map (homotopyMap K L f) =
    (DerivedCategory.quotientCompQhIso C).hom.app K ≫ f ≫
      (DerivedCategory.quotientCompQhIso C).inv.app L := by
  exact (Equiv.ofBijective _ (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) L)).apply_symm_apply _

/-- The representative localizes to the original specified morphism. -/
theorem map_spec : DerivedCategory.Q.map (map K L f) = f := by
  apply (cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app K)).1
  calc
    _ = DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (map K L f)) ≫
        (DerivedCategory.quotientCompQhIso C).hom.app L :=
      ((DerivedCategory.quotientCompQhIso C).hom.naturality (map K L f)).symm
    _ = _ := by
      rw [map, Functor.map_preimage, homotopyMap_spec]
      change ((DerivedCategory.quotientCompQhIso C).hom.app K ≫ f ≫
        (DerivedCategory.quotientCompQhIso C).inv.app L) ≫
          (DerivedCategory.quotientCompQhIso C).hom.app L = _
      simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

end SpecifiedDerivedRepresentative
