module

public import ReasLib.AlgebraicGeometry.Scheme.Size
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped Cardinal AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact scheme monomorphism has source size bounded by target size. -/
theorem size_le_of_mono_quasiCompact {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f]
    [QuasiCompact f] : X.size ≤ Y.size := sorry

/-- A locally finitely presented scheme monomorphism has source size bounded by target size. -/
theorem size_le_of_mono_locallyOfFinitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Mono f] [LocallyOfFinitePresentation f] : X.size ≤ Y.size := sorry

/-- A scheme monomorphism that is quasi-compact or locally of finite presentation has source
size bounded by target size. -/
theorem size_le_of_mono_of_quasiCompact_or_locallyOfFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f]
    (h : QuasiCompact f ∨ LocallyOfFinitePresentation f) :
    X.size ≤ Y.size := sorry

end AlgebraicGeometry.Scheme
