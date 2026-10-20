/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Types
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion

/-!
# Closed immersions from monomorphisms containing the reduction

A representable monomorphism containing the reduction of its target is a closed
immersion if it is locally of finite type or its target is locally Noetherian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion

/-- A representable monomorphism of formal algebraic spaces through which the
target reduction inclusion factors is a closed immersion if it is locally of
finite type or its target is locally Noetherian. -/
@[stacks 0GHZ]
theorem of_mono_of_reduction {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) [Mono f]
    (h_rep : AlgebraicSpace.representableByAlgebraicSpaces f)
    (R : ReductionData Y) (g : R.space.functorOfPoints ⟶ X)
    (h_factor : g ≫ f = R.ι)
    (h_lft_or_noetherian : LocallyOfFiniteType f ∨ IsLocallyNoetherian Y) :
    ClosedImmersion f :=
  sorry

/-- A representable monomorphism of formal algebraic spaces that is locally of
finite type and through which the target reduction inclusion factors is a
closed immersion. -/
theorem of_mono_of_reduction_locallyOfFiniteType {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) [Mono f]
    (h_rep : AlgebraicSpace.representableByAlgebraicSpaces f)
    (R : ReductionData Y) (g : R.space.functorOfPoints ⟶ X)
    (h_factor : g ≫ f = R.ι) (h_lft : LocallyOfFiniteType f) :
    ClosedImmersion f :=
  of_mono_of_reduction f h_rep R g h_factor (Or.inl h_lft)

/-- A representable monomorphism of formal algebraic spaces with locally
Noetherian target through which the target reduction inclusion factors is a
closed immersion. -/
theorem of_mono_of_reduction_locallyNoetherian {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Mono f]
    (h_rep : AlgebraicSpace.representableByAlgebraicSpaces f)
    (R : ReductionData Y) (g : R.space.functorOfPoints ⟶ X)
    (h_factor : g ≫ f = R.ι) :
    ClosedImmersion f :=
  of_mono_of_reduction f h_rep R g h_factor (Or.inr inferInstance)

end AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion
