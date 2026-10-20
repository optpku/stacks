module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeSquare
public import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Uniqueness in the valuative criterion for algebraic stacks

Uniqueness requires exactly one compatible 2-morphism between any two coherent
lifts of a valuative square. It does not require a lift to exist and is stable
under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.ValuativeCriterion

/-- A morphism of algebraic stacks satisfies the uniqueness part of the valuative
criterion if any two coherent lifts of a valuative square have exactly one
2-morphism compatible with both triangular comparisons. -/
@[mk_iff]
class Uniqueness {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- Any two lifts whose triangular comparisons compose to the chosen outer
  comparison have exactly one compatible 2-morphism. -/
  uniqueCompatibleHom :
    ∀ (sq : ValuativeCommSq f) (a a' : GroupoidsOver.slice sq.specR ⟶ X)
      (α : sq.verticalMap ≫ a ≅ sq.i₁) (β : sq.i₂ ≅ a ≫ f)
      (α' : sq.verticalMap ≫ a' ≅ sq.i₁) (β' : sq.i₂ ≅ a' ≫ f),
      whiskerLeftIso sq.verticalMap β ≪≫ (α_ sq.verticalMap a f).symm ≪≫
          whiskerRightIso α f = sq.iso →
      whiskerLeftIso sq.verticalMap β' ≪≫ (α_ sq.verticalMap a' f).symm ≪≫
          whiskerRightIso α' f = sq.iso →
      ∃! θ : a ⟶ a',
        (sq.verticalMap ◁ θ ≫ α'.hom = α.hom) ∧
          (β.hom ≫ θ ▷ f = β'.hom)

namespace Uniqueness

/-- The composition of morphisms of algebraic stacks satisfying uniqueness
again satisfies uniqueness. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Uniqueness f] [Uniqueness g] :
    Uniqueness (f ≫ g) :=
  sorry

end Uniqueness

end AlgebraicGeometry.AlgebraicStack.ValuativeCriterion
