/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Topology.Defs.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison

/-!
# Canonical topology on algebraic-space points

Openness is tested by pullback along representable étale morphisms from schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Points

/-- A morphism from a scheme over `S` induces a map from scheme points to
algebraic-space points. -/
def mapOfOver {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (p : ofOver U ⟶ X) :
    U.left → Points X :=
  fun point ↦ map p (ofOver.pointsEquiv U point)

/-- The map on scheme points is the composite of `ofOver.pointsEquiv` with `Points.map`. -/
@[simp]
theorem mapOfOver_apply {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (p : ofOver U ⟶ X) (point : U.left) :
    mapOfOver p point = map p (ofOver.pointsEquiv U point) := sorry

/-- A subset of algebraic-space points is open when its preimage along every
representable étale morphism from a scheme is open. -/
def isOpen {S : Scheme.{u}} {X : AlgebraicSpace S} (subset : Set (Points X)) : Prop :=
  ∀ ⦃U : Over S⦄ (p : ofOver U ⟶ X),
    (MorphismProperty.over (@Etale)).presheaf p → IsOpen (mapOfOver p ⁻¹' subset)

end Points

/-- The canonical topology on algebraic-space points tests openness along
representable étale morphisms from schemes. -/
instance instTopologicalSpacePoints {S : Scheme.{u}} (X : AlgebraicSpace S) :
    TopologicalSpace (Points X) where
  IsOpen := Points.isOpen
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

end AlgebraicGeometry.AlgebraicSpace
