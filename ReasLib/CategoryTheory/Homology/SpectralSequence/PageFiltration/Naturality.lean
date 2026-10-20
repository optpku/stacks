/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageFiltration

/-!
# Naturality of spectral-sequence page filtrations

The page-filtration owner exposes the cycle and boundary maps, while this leaf supplies the
small functorial API used by downstream constructions.  Keeping these statements separate avoids
making the quotient and limit-stage definitions depend on a large naturality import.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type*} {c : ℤ → ComplexShape κ}

/-! ## Cycle and boundary maps -/

namespace Cycle

/- The identity and composition laws are deliberately stated at the spectral-sequence layer;
   clients should not have to unfold the corresponding `HomologyPageTower` map. -/

/-- The cycle-stage map induced by an identity spectral-sequence morphism is the identity. -/
@[simp, stacks 011O "identity map on a spectral-sequence cycle stage"]
theorem map_id (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    map (𝟙 E) pq r = 𝟙 (E.cycle pq r : C) := sorry

/-- Cycle-stage maps preserve composition of spectral-sequence morphisms. -/
@[simp, stacks 011O "composition of spectral-sequence cycle-stage maps"]
theorem map_comp {E E' E'' : SpectralSequence C c 1}
    (f : E ⟶ E') (g : E' ⟶ E'') (pq : κ) (r : ℕ+) :
    map (f ≫ g) pq r = map f pq r ≫ map g pq r := sorry

/-- A cycle-stage map is an isomorphism when the ambient spectral-sequence map is. -/
@[stacks 011O "isomorphism on spectral-sequence cycle stages"]
noncomputable instance map_isIso {E E' : SpectralSequence C c 1}
    (f : E ⟶ E') (pq : κ) (r : ℕ+) [IsIso f] :
    IsIso (map f pq r) := sorry

/-- The cycle-stage construction at fixed grading and page is functorial. -/
@[stacks 011O "cycle-stage functor of a spectral sequence"]
noncomputable def functor (pq : κ) (r : ℕ+) :
    SpectralSequence C c 1 ⥤ C where
  obj E := E.cycle pq r
  map f := map f pq r
  map_id E := map_id E pq r
  map_comp f g := map_comp f g pq r

namespace Functor

/-- Evaluation of the cycle-stage functor on objects. -/
@[simp]
theorem obj (pq : κ) (r : ℕ+) (E : SpectralSequence C c 1) :
    (functor (C := C) (c := c) pq r).obj E = E.cycle pq r := rfl

/-- Evaluation of the cycle-stage functor on morphisms. -/
@[simp]
theorem map (pq : κ) (r : ℕ+)
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') :
    (functor (C := C) (c := c) pq r).map f = Cycle.map f pq r := rfl

end Functor

end Cycle

namespace Boundary

/-- The boundary-stage map induced by an identity spectral-sequence morphism is the identity. -/
@[simp, stacks 011O "identity map on spectral-sequence boundary stages"]
theorem map_id (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    map (𝟙 E) pq r = 𝟙 (E.boundary pq r : C) := sorry

/-- Boundary-stage maps preserve composition of spectral-sequence morphisms. -/
@[simp, stacks 011O "composition of spectral-sequence boundary-stage maps"]
theorem map_comp {E E' E'' : SpectralSequence C c 1}
    (f : E ⟶ E') (g : E' ⟶ E'') (pq : κ) (r : ℕ+) :
    map (f ≫ g) pq r = map f pq r ≫ map g pq r := sorry

/-- A boundary-stage map is an isomorphism when the ambient spectral-sequence map is. -/
@[stacks 011O "isomorphism on spectral-sequence boundary stages"]
noncomputable instance map_isIso {E E' : SpectralSequence C c 1}
    (f : E ⟶ E') (pq : κ) (r : ℕ+) [IsIso f] :
    IsIso (map f pq r) := sorry

/-- The boundary-stage construction at fixed grading and page is functorial. -/
@[stacks 011O "boundary-stage functor of a spectral sequence"]
noncomputable def functor (pq : κ) (r : ℕ+) :
    SpectralSequence C c 1 ⥤ C where
  obj E := E.boundary pq r
  map f := map f pq r
  map_id E := map_id E pq r
  map_comp f g := map_comp f g pq r

namespace Functor

/-- Evaluation of the boundary-stage functor on objects. -/
@[simp]
theorem obj (pq : κ) (r : ℕ+) (E : SpectralSequence C c 1) :
    (functor (C := C) (c := c) pq r).obj E = E.boundary pq r := rfl

/-- Evaluation of the boundary-stage functor on morphisms. -/
@[simp]
theorem map (pq : κ) (r : ℕ+)
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') :
    (functor (C := C) (c := c) pq r).map f = Boundary.map f pq r := rfl

end Functor

/-- The canonical map from a boundary stage to its page entry. -/
noncomputable abbrev toPage (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    (E.boundary pq r : C) ⟶ E⟦r, pq⟧ :=
  Subobject.ofLE (E.boundary pq r) (E.cycle pq r) (E.boundary_le_cycle pq r) ≫
    E.cycleToPage pq r

/-- Boundary-stage maps commute with the canonical map to the corresponding page entry. -/
@[reassoc, stacks 011O "naturality of the boundary-stage map to a page"]
theorem toPage_naturality
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) :
    map f pq r ≫ toPage E' pq r =
      toPage E pq r ≫ (f.positivePage r).f pq := sorry

end Boundary

end SpectralSequence
end CategoryTheory
