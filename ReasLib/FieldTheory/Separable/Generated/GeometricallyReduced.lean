module

public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Separable.Generated.Properties

@[expose] public section

/-!
# Geometric Reducedness of Separable-Over Field Extensions

This leaf relates the separable-over field-extension predicate
`Algebra.IsSeparableOver` to the canonical algebra predicate
`Algebra.IsGeometricallyReduced`.  The consequences are theorems rather than
instances: separability over the base is useful as explicit mathematical data,
and making its geometric consequences global would add noncanonical typeclass
search paths.
-/

namespace Algebra.IsSeparableOver

universe u v

variable {k : Type u} {K : Type v}
variable [Field k] [Field K] [Algebra k K]

/-- A field extension separable over its base is geometrically reduced over that base. -/
@[stacks 030U]
theorem isGeometricallyReduced [IsSeparableOver k K] :
    Algebra.IsGeometricallyReduced k K := sorry

/-- Explicit-hypothesis form of `isGeometricallyReduced`; use this bridge when separability is
available as a proposition value rather than an installed instance. -/
@[stacks 030U "explicit hypothesis bridge"]
theorem isGeometricallyReduced_of (hsep : IsSeparableOver k K) :
    Algebra.IsGeometricallyReduced k K := sorry

/-- For any field extension, separability over the base is equivalent to geometric reducedness
of the target field over its base. -/
@[stacks 030U "field-target equivalence"]
theorem iff_isGeometricallyReduced :
    IsSeparableOver k K ↔ Algebra.IsGeometricallyReduced k K := sorry

end Algebra.IsSeparableOver

namespace Algebra.IsSeparableOver.CharP

universe u v

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable {p : ℕ} [Fact p.Prime] [CharP k p]

/-- In characteristic `p`, separability over the base is equivalent to
geometric reducedness of the target field over its base. -/
@[stacks 030W]
theorem iff_isGeometricallyReduced :
    Algebra.IsSeparableOver k K ↔ Algebra.IsGeometricallyReduced k K := sorry

end Algebra.IsSeparableOver.CharP
