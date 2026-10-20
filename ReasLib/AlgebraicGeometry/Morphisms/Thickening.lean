module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Thickening.Hom

/-- The closed and ambient maps of a morphism of thickenings are simultaneously affine. -/
theorem isAffineHom_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    IsAffineHom g.left ↔ IsAffineHom g.right := sorry

/-- The closed and ambient maps of a morphism of thickenings are simultaneously surjective. -/
theorem surjective_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    Surjective g.left ↔ Surjective g.right := sorry

/-- The closed and ambient maps of a morphism of thickenings are simultaneously quasi-compact. -/
theorem quasiCompact_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    QuasiCompact g.left ↔ QuasiCompact g.right := sorry

/-- The closed and ambient maps of a morphism of thickenings are simultaneously universally
closed. -/
theorem universallyClosed_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    UniversallyClosed g.left ↔ UniversallyClosed g.right := sorry

/-- The closed and ambient maps of a morphism of thickenings are simultaneously integral. -/
theorem isIntegralHom_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    IsIntegralHom g.left ↔ IsIntegralHom g.right := sorry

/-- The closed and ambient maps of a morphism of thickenings are simultaneously separated. -/
theorem isSeparated_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    IsSeparated g.left ↔ IsSeparated g.right := sorry

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
quasi-separated. -/
theorem quasiSeparated_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    QuasiSeparated g.left ↔ QuasiSeparated g.right := sorry

/-- The closed and ambient maps of a morphism of thickenings are simultaneously universally
injective. -/
theorem universallyInjective_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    UniversallyInjective g.left ↔ UniversallyInjective g.right := sorry

/-- The closed and ambient maps of a morphism of thickenings are simultaneously universally
open. -/
theorem universallyOpen_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    UniversallyOpen g.left ↔ UniversallyOpen g.right := sorry

/-- The closed and ambient maps of a morphism of thickenings are simultaneously quasi-affine. -/
theorem quasiAffineHom_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    QuasiAffineHom g.left ↔ QuasiAffineHom g.right := sorry

end AlgebraicGeometry.Thickening.Hom
