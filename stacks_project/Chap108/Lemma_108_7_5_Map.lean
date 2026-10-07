module

public import stacks_project.Chap99.«99_9_1_1_Functor»
public import stacks_project.Chap108.Lemma_108_5_4_Map

/-!
# The Hilbert functor map along a closed immersion

A closed immersion `π : X ⟶ Y` of algebraic spaces over `B` induces a
comparison `X_T ⟶ Y_T` on fibres and a natural transformation
`hilbert (π ≫ y) ⟶ hilbert y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite
open AlgebraicGeometry.AlgebraicSpace.Quot (SchemesOver)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S}

/-- The fibre comparison of a closed immersion is a closed immersion. -/
instance instIsClosedImmersion_fiberComparison (π : X ⟶ Y) (y : Y ⟶ B)
    (σ : SchemesOver B) [IsClosedImmersion π] :
    IsClosedImmersion (Quot.fiberComparison π y σ) :=
  sorry

namespace Point

/-- View a Hilbert point of `X_T` as a Hilbert point of `Y_T` along a closed
immersion `π`, using that `y : Y ⟶ B` is separated. -/
def closedPushforward (π : X ⟶ Y) (y : Y ⟶ B) {σ : SchemesOver B}
    [IsClosedImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (p : Point (π ≫ y) σ) : Point y σ where
  subspace :=
    { X := p.subspace.X
      ι := p.subspace.ι ≫ Quot.fiberComparison π y σ
      isClosedImmersion := sorry }
  isFinitePresentation := sorry
  isFlat := sorry
  isProper := sorry

/-- The inclusion of a closed-pushed Hilbert point is the original inclusion
composed with the fibre comparison, using that `y` is separated. -/
theorem closedPushforward_ι (π : X ⟶ Y) (y : Y ⟶ B) {σ : SchemesOver B}
    [IsClosedImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (p : Point (π ≫ y) σ) :
    (closedPushforward π y p).subspace.ι =
      p.subspace.ι ≫ Quot.fiberComparison π y σ :=
  sorry

/-- A closed-pushed Hilbert point remains a closed subspace of `Y_T` whose
structure map to `T` is of finite presentation, flat, and proper, using that
`y` is separated. -/
theorem closedPushforward_spec (π : X ⟶ Y) (y : Y ⟶ B) {σ : SchemesOver B}
    [IsClosedImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (p : Point (π ≫ y) σ) :
    IsClosedImmersion (closedPushforward π y p).subspace.ι ∧
      FinitePresentation (closedPushforward π y p).structureMap ∧
      Flat (closedPushforward π y p).structureMap ∧
      Proper (closedPushforward π y p).structureMap :=
  sorry

end Point

/-- Closed pushforward of Hilbert points preserves ideal-sheaf identification,
using that `y` is separated. -/
theorem Rel_closedPushforward (π : X ⟶ Y) (y : Y ⟶ B)
    [IsClosedImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (σ : SchemesOver B) :
    ∀ (p q : Point (π ≫ y) σ),
      (setoid (π ≫ y) σ).r p q →
        (setoid y σ).r (Point.closedPushforward π y p)
          (Point.closedPushforward π y q) :=
  sorry

/-- The natural transformation `Hilb_{X/B} ⟶ Hilb_{Y/B}` induced by a closed
immersion `π : X ⟶ Y` of algebraic spaces with `y : Y ⟶ B` separated. -/
def closedMap (π : X ⟶ Y) (y : Y ⟶ B)
    [IsClosedImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] :
    hilbert (π ≫ y) ⟶ hilbert y where
  app σ :=
    TypeCat.ofHom
      (_root_.Quotient.map
        (fun p : Point (π ≫ y) σ.unop ↦ Point.closedPushforward π y p)
        (Rel_closedPushforward π y σ.unop))
  naturality := sorry

/-- The component of `closedMap π y` at a scheme over `B` is the quotient map of
`Point.closedPushforward`, using that `y` is separated. -/
theorem closedMap_app (π : X ⟶ Y) (y : Y ⟶ B)
    [IsClosedImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (σ : (SchemesOver B)ᵒᵖ) :
    (closedMap π y).app σ =
      TypeCat.ofHom
        (_root_.Quotient.map
          (fun p : Point (π ≫ y) σ.unop ↦ Point.closedPushforward π y p)
          (Rel_closedPushforward π y σ.unop)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
