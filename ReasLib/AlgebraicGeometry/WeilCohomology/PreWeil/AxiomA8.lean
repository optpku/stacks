module

public import Mathlib.CategoryTheory.Category.ULift
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalSections
public import ReasLib.AlgebraicGeometry.WeilCohomology.GradedPullback

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace WeilCohomology.PreWeilTheory

/-- A pre-Weil theory satisfies Axiom A8 when degree-`(0, 0)` pullback along the canonical
map to `Spec Γ(Y, 𝒪_Y)` is bijective for every smooth projective scheme over the base field. -/
def SatisfiesAxiomA8
    {k : Type u} [Field k]
    {F : Type v} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {H Picard Cycle : ULiftHom.{u + 1} (SchemeOverField k) → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine (ULiftHom.{u + 1} (SchemeOverField k)) H Picard Cycle) :
    Prop :=
  ∀ Y : SchemeOverField k, T.IsSmoothProjective (ULiftHom.up.obj Y) →
    Function.Bijective
      (T.pullbackGrade
        (ULiftHom.up.map (AlgebraicGeometry.SchemeOverField.toGlobalSectionsSpec Y)) (0, 0))

/-- Axiom A8 unfolds to bijectivity of canonical degree-zero pullback on every smooth
projective scheme over the base field. -/
theorem satisfiesAxiomA8_iff
    {k : Type u} [Field k]
    {F : Type v} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {H Picard Cycle : ULiftHom.{u + 1} (SchemeOverField k) → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine (ULiftHom.{u + 1} (SchemeOverField k)) H Picard Cycle) :
    T.SatisfiesAxiomA8 ↔
      ∀ Y : SchemeOverField k, T.IsSmoothProjective (ULiftHom.up.obj Y) →
        Function.Bijective
          (T.pullbackGrade
            (ULiftHom.up.map (AlgebraicGeometry.SchemeOverField.toGlobalSectionsSpec Y))
            (0, 0)) := sorry

end WeilCohomology.PreWeilTheory
