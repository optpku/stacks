module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.Action

/-!
# Source compatibility for the affine-line translation action

The source-facing names for the base and affine-line cover are retained as definitional aliases;
the action itself is owned by the reusable affine-line translation module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation

/-- The source-facing base alias for the canonical affine-line quotient presentation. -/
abbrev base (k : Type u) [Field k] [CharZero k] : Scheme.{u} :=
  AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.base k

/-- The source-facing cover alias for the canonical affine-line quotient presentation. -/
abbrev cover (k : Type u) [Field k] [CharZero k] : Over (base k) :=
  AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.cover k

#check (action : ∀ (k : Type u) [Field k] [CharZero k],
  group →* Aut (cover k))

end AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation
