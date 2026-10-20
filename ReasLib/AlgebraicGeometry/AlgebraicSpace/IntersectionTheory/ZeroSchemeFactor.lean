module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ZeroSection

/-! Actual maps into the zero subspace from vanishing of the restricted section. -/
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ZeroSchemeFactor

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (L : X.Modules) [CategoryTheory.MonoidalCategory.isInvertibleObject L]
    (s : L.sections) (g : Y ⟶ X)

/-- Scheme-theoretic vanishing, using the actual pulled-back section morphism. -/
def VanishesOn : Prop := (Modules.pullback g).map (regularSectionHom L s) = 0

/-- Pullback of the image of the dual section is zero on every test of a map
on which the section vanishes. This is a law of the specified pullback and ideal. -/
theorem test_vanishes (h : VanishesOn L s g) (T : (Over S)ᵒᵖ)
    (y : Y.functorOfPoints.obj T) :
    vanishes (homOfPoint (g.app T y)) (zeroIdealSubobject L s) := by
  sorry

/-- The factor sends the actual test point g(y) to the zero-ideal subtype. -/
def lift (h : VanishesOn L s g) : Y ⟶ (zeroScheme L s).X where
  app T := TypeCat.ofHom fun y ↦ ⟨g.app T y, test_vanishes L s g h T y⟩
  naturality T T' a := by
    ext y
    apply Subtype.ext
    exact congrArg (fun t : Y.functorOfPoints.obj T ⟶ X.functorOfPoints.obj T' ↦ t y)
      (g.naturality a)

@[simp] theorem lift_ι (h : VanishesOn L s g) :
    lift L s g h ≫ zeroSchemeι L s = g := rfl

@[simp] theorem lift_app (h : VanishesOn L s g) (T : (Over S)ᵒᵖ)
    (y : Y.functorOfPoints.obj T) :
    ((lift L s g h).app T y).val = g.app T y := rfl

/-- A section vanishes after pullback precisely when the morphism factors
through its zero subspace (Stacks 0846 (2)). -/
theorem vanishesOn_iff_factors :
    VanishesOn L s g ↔ ∃ a : Y ⟶ (zeroScheme L s).X, a ≫ zeroSchemeι L s = g :=
  sorry

theorem lift_unique (h : VanishesOn L s g) (a : Y ⟶ (zeroScheme L s).X)
    (ha : a ≫ zeroSchemeι L s = g) : a = lift L s g h := by
  -- Local instance justification (defeq pin): Uniqueness cancels the inclusion of this zero scheme using its own monomorphism certificate.
  letI : Mono (zeroSchemeι L s) := (ClosedSubspace.spec (zeroScheme L s)).2
  apply (cancel_mono (zeroSchemeι L s)).mp
  exact ha.trans (lift_ι L s g h).symm

/-- A closed immersion factoring through another closed immersion remains closed. -/
theorem lift_isClosedImmersion [IsClosedImmersion g] (h : VanishesOn L s g) :
    IsClosedImmersion (lift L s g h) := by
  -- Local instance justification (defeq pin): The of_comp argument factors through this particular zero-scheme inclusion, so use its recorded closed-immersion certificate.
  letI : IsClosedImmersion (zeroSchemeι L s) := (zeroScheme L s).isClosedImmersion
  exact AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.of_comp
    g (zeroSchemeι L s) (lift L s g h) (lift_ι L s g h)

/-- The actual zero section under the structure-module/section equivalence. -/
def zeroSection : L.sections := L.unitHomEquiv 0

/-- For the zero section the branch condition holds for every g, without an
added trivialization or hypothesis on the line bundle. -/
theorem vanishesOn_zero : VanishesOn L (zeroSection L) g := by
  -- Local instance justification (proof-local temporary data): Derive preservation of zero from the canonical module pullback adjunction for this morphism g.
  letI : (Modules.pullback g).IsLeftAdjoint :=
    (Modules.pullbackPushforwardAdjunction g).isLeftAdjoint
  change (Modules.pullback g).map
    (L.unitHomEquiv.symm (L.unitHomEquiv 0)) = 0
  rw [Equiv.symm_apply_apply]
  exact Functor.map_zero _ _ _

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ZeroSchemeFactor
