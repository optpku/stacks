module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Graph

/-!
# Sections of scheme morphisms
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.Section

variable {X S : Scheme.{u}} {f : X ⟶ S} {s : S ⟶ X}

/-- A section of a scheme morphism is an immersion. -/
@[stacks 01KT]
theorem isImmersion (fac : s ≫ f = 𝟙 S) : IsImmersion s := sorry

/-- A section of a separated scheme morphism is a closed immersion. -/
@[stacks 01KT]
theorem isClosedImmersion [IsSeparated f] (fac : s ≫ f = 𝟙 S) :
    IsClosedImmersion s := sorry

/-- A section of a quasi-separated scheme morphism is quasi-compact. -/
@[stacks 01KT]
theorem quasiCompact [QuasiSeparated f] (fac : s ≫ f = 𝟙 S) :
    QuasiCompact s := sorry

end AlgebraicGeometry.Scheme.Hom.Section
