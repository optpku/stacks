/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.CategoryTheory.InverseSystem.Cone

/-!
# Positive formal neighborhoods

For ideal-sheaf data `E` on a scheme, this module constructs the positive infinitesimal
neighborhoods cut out by `E ^ (n + 1)`, their inverse system of global-section rings, its limit,
and the canonical projections from that limit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FormalNeighborhood

variable {X : Scheme.{u}}

/-- Positive formal-neighborhood stage `n`, cut out by `E ^ (n + 1)`. -/
abbrev stage (E : X.IdealSheafData) (n : ℕ) : Scheme.{u} :=
  (E ^ (n + 1)).subscheme

/-- A positive formal-neighborhood stage is the subscheme cut out by the corresponding positive
power of its ideal sheaf. -/
theorem stage_def (E : X.IdealSheafData) (n : ℕ) :
    stage E n = (E ^ (n + 1)).subscheme := sorry

/-- The next ideal power is contained in the current power after transport along the identity. -/
theorem powerSucc_le_mapId (E : X.IdealSheafData) (n : ℕ) :
    E ^ (n + 1 + 1) ≤ (E ^ (n + 1)).map (𝟙 X) := sorry

/-- The canonical closed immersion from one positive formal-neighborhood stage into the next. -/
def inclusion (E : X.IdealSheafData) (n : ℕ) : stage E n ⟶ stage E (n + 1) :=
  IdealSheafData.subschemeMap (E ^ (n + 1)) (E ^ (n + 1 + 1)) (𝟙 X)
    (powerSucc_le_mapId E n)

/-- The stage inclusion commutes with both closed immersions into the ambient scheme. -/
theorem inclusion_subschemeι (E : X.IdealSheafData) (n : ℕ) :
    inclusion E n ≫ (E ^ (n + 1 + 1)).subschemeι = (E ^ (n + 1)).subschemeι := sorry

/-- The global-section ring of positive formal-neighborhood stage `n`. -/
abbrev sectionRing (E : X.IdealSheafData) (n : ℕ) : CommRingCat.{u} :=
  Scheme.globalSectionsRing (stage E n)

/-- The stage section ring is the ring of global functions on that stage. -/
theorem sectionRing_def (E : X.IdealSheafData) (n : ℕ) :
    sectionRing E n = Scheme.globalSectionsRing (stage E n) := sorry

/-- Restriction of global functions along a successor-stage inclusion. -/
abbrev sectionStep (E : X.IdealSheafData) (n : ℕ) :
    sectionRing E (n + 1) ⟶ sectionRing E n :=
  (inclusion E n).appTop

/-- The section transition is pullback along the corresponding stage inclusion. -/
theorem sectionStep_def (E : X.IdealSheafData) (n : ℕ) :
    sectionStep E n = (inclusion E n).appTop := sorry

/-- The inverse system of global-section rings of the positive formal neighborhoods. -/
def sectionSystem (E : X.IdealSheafData) : SequentialInverseSystem CommRingCat.{u} :=
  Functor.ofOpSequence (sectionStep E)

/-- Stage `n` of the section system is the ring of global functions on `stage E n`. -/
theorem sectionSystem_obj (E : X.IdealSheafData) (n : ℕ) :
    (sectionSystem E).obj (op n) = Scheme.globalSectionsRing (stage E n) := sorry

/-- A successor transition in the section system is pullback along the corresponding stage
inclusion. -/
theorem sectionSystem_stepMap (E : X.IdealSheafData) (n : ℕ) :
    (sectionSystem E).stepMap n = (inclusion E n).appTop := sorry

/-- The formal-neighborhood ring is the inverse limit of the positive-stage section rings. -/
noncomputable def ring (E : X.IdealSheafData) : CommRingCat.{u} :=
  limit (sectionSystem E)

/-- The formal-neighborhood ring is the selected categorical limit of its section system. -/
theorem ring_eq_limit (E : X.IdealSheafData) :
    ring E = limit (sectionSystem E) := sorry

/-- The canonical projection from the formal-neighborhood ring to positive stage `n`. -/
noncomputable def projection (E : X.IdealSheafData) (n : ℕ) :
    ring E ⟶ (sectionSystem E).obj (op n) :=
  limit.π (sectionSystem E) (op n)

/-- The stage projection is the corresponding leg of the selected limit cone. -/
theorem projection_def (E : X.IdealSheafData) (n : ℕ) :
    projection E n = limit.π (sectionSystem E) (op n) := sorry

/-- Limit projections commute with every successor restriction map. -/
theorem projection_step (E : X.IdealSheafData) (n : ℕ) :
    projection E (n + 1) ≫ (sectionSystem E).stepMap n = projection E n := sorry

end AlgebraicGeometry.Scheme.FormalNeighborhood
