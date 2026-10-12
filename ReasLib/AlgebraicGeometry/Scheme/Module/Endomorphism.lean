/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.CategoryTheory.Monoidal.Closed.TensorInternalHom

/-!
# Internal endomorphism comparison maps

This file provides tensoring and conjugation maps for internal endomorphism objects of scheme
modules.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}}

/-- Tensoring a scheme module by `L` sends its internal endomorphisms to the internal
endomorphisms of the tensor product. -/
noncomputable def tensorEndMap (F L : S.Modules) :
    internalHom F F ⟶ internalHom (F ⊗ L) (F ⊗ L) :=
  (ρ_ (internalHom F F)).inv ≫
    (𝟙 (internalHom F F) ⊗ₘ MonoidalClosed.id L) ≫
      tensorHomComparison F F L L

/-- The tensor-on-endomorphisms map is given by the canonical closed-category comparison
composite. -/
theorem tensorEndMap_spec (F L : S.Modules) :
    tensorEndMap F L =
      (ρ_ (internalHom F F)).inv ≫
        (𝟙 (internalHom F F) ⊗ₘ MonoidalClosed.id L) ≫
          tensorHomComparison F F L L := sorry

/-- Conjugation along a scheme-module isomorphism identifies the two internal endomorphism
objects. -/
noncomputable def conjEndIso {A B : S.Modules} (e : A ≅ B) :
    internalHom A A ≅ internalHom B B where
  hom := (MonoidalClosed.pre e.inv).app A ≫ (ihom B).map e.hom
  inv := (MonoidalClosed.pre e.hom).app B ≫ (ihom A).map e.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward morphism of conjugation is precomposition by `e.inv` followed by postcomposition
by `e.hom`. -/
theorem conjEndIso_hom {A B : S.Modules} (e : A ≅ B) :
    (conjEndIso e).hom = (MonoidalClosed.pre e.inv).app A ≫ (ihom B).map e.hom := sorry

/-- The inverse morphism of conjugation is precomposition by `e.hom` followed by postcomposition
by `e.inv`. -/
theorem conjEndIso_inv {A B : S.Modules} (e : A ≅ B) :
    (conjEndIso e).inv = (MonoidalClosed.pre e.hom).app B ≫ (ihom A).map e.inv := sorry

end AlgebraicGeometry.Scheme.Modules
