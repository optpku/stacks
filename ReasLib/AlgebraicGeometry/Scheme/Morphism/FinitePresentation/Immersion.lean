module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Open immersions of finite presentation

For an open immersion, local finite presentation and quasi-separatedness are canonical.  Thus the
project-level finite-presentation condition is exactly quasi-compactness.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An open immersion with quasi-compact source over its target is of finite presentation. -/
theorem FinitePresentation.of_isOpenImmersion
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsOpenImmersion f]
    (h_quasiCompact : QuasiCompact f) :
    FinitePresentation f := sorry

/-- A quasi-compact open immersion is canonically a finite-presentation morphism. -/
instance instFinitePresentationOfIsOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] [QuasiCompact f] :
    FinitePresentation f := sorry

/-- Lemma 29.21.6: an open immersion is of finite presentation exactly when it is quasi-compact. -/
@[stacks 01TU]
theorem finitePresentation_iff_quasiCompact_of_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    FinitePresentation f ↔ QuasiCompact f := sorry

end AlgebraicGeometry.Scheme.Hom
