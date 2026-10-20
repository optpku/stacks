module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Support
public import ReasLib.CategoryTheory.ObjectProperty.Retract.Lattice

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

/-- Perfect derived `𝒪_X`-modules whose cohomology is supported on `T`. -/
abbrev perfectSupportedOn (T : Set X) : ObjectProperty (ModuleDerived X) :=
  perfect ⊓ supportedOn T

/-- Membership in `perfectSupportedOn T` is perfectness together with cohomological support on
`T`. -/
theorem perfectSupportedOn_iff (T : Set X) (K : ModuleDerived X) :
    perfectSupportedOn T K ↔ IsPerfect K ∧ IsSupportedOn K T := sorry

/-- The full subcategory of perfect derived `𝒪_X`-modules supported on `T`. -/
abbrev PerfectSupportedOn (T : Set X) :=
  (perfectSupportedOn T).FullSubcategory

/-- Supported perfect derived modules are closed under isomorphisms. -/
instance perfectSupportedOn_isClosedUnderIsomorphisms (T : Set X) :
    (perfectSupportedOn T).IsClosedUnderIsomorphisms := sorry

/-- Supported perfect derived modules form a triangulated object property. -/
instance perfectSupportedOn_isTriangulated (T : Set X) :
    (perfectSupportedOn T).IsTriangulated := sorry

/-- Supported perfect derived modules are stable under retracts. -/
instance perfectSupportedOn_isStableUnderRetracts (T : Set X) :
    (perfectSupportedOn T).IsStableUnderRetracts := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
