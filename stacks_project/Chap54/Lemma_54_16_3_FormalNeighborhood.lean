/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FormalNeighborhood

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FormalNeighborhood

variable {X : Scheme.{u}}

#check (stage : ∀ {X : Scheme.{u}}, X.IdealSheafData → ℕ → Scheme.{u})
#check (stage_def : ∀ {X : Scheme.{u}} (E : X.IdealSheafData) (n : ℕ),
  stage E n = (E ^ (n + 1)).subscheme)
#check (powerSucc_le_mapId : ∀ {X : Scheme.{u}} (E : X.IdealSheafData) (n : ℕ),
  E ^ (n + 1 + 1) ≤ (E ^ (n + 1)).map (𝟙 X))
#check (inclusion : ∀ {X : Scheme.{u}} (E : X.IdealSheafData) (n : ℕ),
  stage E n ⟶ stage E (n + 1))
#check (inclusion_subschemeι : ∀ {X : Scheme.{u}} (E : X.IdealSheafData) (n : ℕ),
  inclusion E n ≫ (E ^ (n + 1 + 1)).subschemeι = (E ^ (n + 1)).subschemeι)
#check (sectionRing : ∀ {X : Scheme.{u}}, X.IdealSheafData → ℕ → CommRingCat.{u})
#check (sectionRing_def : ∀ {X : Scheme.{u}} (E : X.IdealSheafData) (n : ℕ),
  sectionRing E n = Scheme.globalSectionsRing (stage E n))
#check (sectionStep : ∀ {X : Scheme.{u}} (E : X.IdealSheafData) (n : ℕ),
  sectionRing E (n + 1) ⟶ sectionRing E n)
#check (sectionStep_def : ∀ {X : Scheme.{u}} (E : X.IdealSheafData) (n : ℕ),
  sectionStep E n = (inclusion E n).appTop)
#check (sectionSystem : ∀ {X : Scheme.{u}}, X.IdealSheafData →
  SequentialInverseSystem CommRingCat.{u})
#check (sectionSystem_obj : ∀ {X : Scheme.{u}} (E : X.IdealSheafData) (n : ℕ),
  (sectionSystem E).obj (op n) = Scheme.globalSectionsRing (stage E n))
#check (sectionSystem_stepMap : ∀ {X : Scheme.{u}} (E : X.IdealSheafData) (n : ℕ),
  (sectionSystem E).stepMap n = (inclusion E n).appTop)
#check (ring : ∀ {X : Scheme.{u}}, X.IdealSheafData → CommRingCat.{u})
#check (ring_eq_limit : ∀ {X : Scheme.{u}} (E : X.IdealSheafData),
  ring E = CategoryTheory.Limits.limit (sectionSystem E))
#check (projection : ∀ {X : Scheme.{u}} (E : X.IdealSheafData) (n : ℕ),
  ring E ⟶ (sectionSystem E).obj (op n))
#check (projection_def : ∀ {X : Scheme.{u}} (E : X.IdealSheafData) (n : ℕ),
  projection E n = CategoryTheory.Limits.limit.π (sectionSystem E) (op n))
#check (projection_step : ∀ {X : Scheme.{u}} (E : X.IdealSheafData) (n : ℕ),
  projection E (n + 1) ≫ (sectionSystem E).stepMap n = projection E n)

end AlgebraicGeometry.Scheme.FormalNeighborhood
