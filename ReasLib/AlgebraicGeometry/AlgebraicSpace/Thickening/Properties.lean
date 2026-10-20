/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Arrow
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen

/-!
# Transfer of morphism properties along morphisms of thickenings

A morphism of thickenings of algebraic spaces over a scheme has a closed
map and an ambient map, and the listed morphism properties hold for one
if and only if they hold for the other.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Thickening.Hom

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
affine. -/
theorem affine_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U) :
    Affine g.left ↔ Affine g.right := sorry

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
surjective. -/
theorem surjective_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U) :
    Surjective g.left ↔ Surjective g.right := sorry

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
quasi-compact. -/
theorem quasiCompact_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U) :
    QuasiCompact g.left ↔ QuasiCompact g.right := sorry

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
universally closed. -/
theorem universallyClosed_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U) :
    UniversallyClosed g.left ↔ UniversallyClosed g.right := sorry

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
integral. -/
theorem isIntegralHom_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U) :
    IsIntegralHom g.left ↔ IsIntegralHom g.right := sorry

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
separated. -/
theorem separated_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U) :
    Separated g.left ↔ Separated g.right := sorry

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
quasi-separated. -/
theorem quasiSeparated_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U) :
    QuasiSeparated g.left ↔ QuasiSeparated g.right := sorry

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
universally injective. -/
theorem universallyInjective_iff {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) :
    UniversallyInjective g.left ↔ UniversallyInjective g.right := sorry

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
universally open. -/
theorem universallyOpen_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U) :
    UniversallyOpen g.left ↔ UniversallyOpen g.right := sorry

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
representable. -/
theorem relativelyRepresentable_iff {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) :
    yoneda.relativelyRepresentable g.left ↔
      yoneda.relativelyRepresentable g.right := sorry

end AlgebraicGeometry.AlgebraicSpace.Thickening.Hom
