/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteComplexQuotient

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
noncomputable section
universe u v

namespace OpenQuotientInflation
variable (R : Type u) [Ring R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (N : OpenNormalSubgroup G)

/-- An action inflated from THIS specified open quotient is discrete. -/
theorem action_open (M : Action (ModuleCat.{max u v} R) (G ⧸ N.toSubgroup)) :
    openStabilizer R G ((Action.res (ModuleCat.{max u v} R)
      (QuotientGroup.mk' N.toSubgroup)).obj M) := by sorry

/-- Actual coefficient-preserving inflation, with openness proved for the given quotient. -/
def functor : Action (ModuleCat.{max u v} R) (G ⧸ N.toSubgroup) ⥤ DiscreteModuleCat R G where
  obj M := ⟨(Action.res (ModuleCat.{max u v} R) (QuotientGroup.mk' N.toSubgroup)).obj M,
    action_open R G N M⟩
  map f := ObjectProperty.homMk
    ((Action.res (ModuleCat.{max u v} R) (QuotientGroup.mk' N.toSubgroup)).map f)
  map_id := by intros; rfl
  map_comp := by intros; rfl

instance functor_additive : (functor R G N).Additive := by sorry
instance functor_preservesHomology : (functor R G N).PreservesHomology := by sorry

end OpenQuotientInflation
