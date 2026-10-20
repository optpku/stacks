module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Power
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder

/-!
# Finite-order thickenings of algebraic spaces

A closed immersion of algebraic spaces is a finite-order thickening when the
associated quasi-coherent ideal sheaf is nilpotent, and an `n`th-order
thickening when the `(n + 1)`st power of that ideal sheaf vanishes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is a finite-order thickening if it is a closed
immersion whose associated ideal sheaf is nilpotent. -/
class IsFiniteOrderThickening {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') : Prop where
  /-- The defining morphism is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion i
  /-- Some positive power of the associated ideal sheaf vanishes. -/
  exists_pow_succ_eq_zero :
    ∃ n, (Hom.idealSheafSubobject i).pow_eq_bot (n + 1)

/-- A morphism of algebraic spaces is a finite-order thickening if and only if it
is a closed immersion whose associated ideal sheaf is nilpotent. -/
theorem isFiniteOrderThickening_iff {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') :
    IsFiniteOrderThickening i ↔
      IsClosedImmersion i ∧
        ∃ n, (Hom.idealSheafSubobject i).pow_eq_bot (n + 1) :=
  sorry

namespace IsFiniteOrderThickening

/-- The identity morphism of an algebraic space is a finite-order thickening. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsFiniteOrderThickening (𝟙 X) :=
  sorry

/-- A finite-order thickening of algebraic spaces is a closed immersion. -/
instance instIsClosedImmersion {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [h : IsFiniteOrderThickening i] : IsClosedImmersion i :=
  h.isClosedImmersion

/-- A finite-order thickening of algebraic spaces is a thickening. -/
instance instIsThickening {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsFiniteOrderThickening i] : IsThickening i :=
  sorry

end IsFiniteOrderThickening

/-- An `n`th-order thickening is a closed immersion whose associated ideal sheaf
has vanishing `(n + 1)`st power. -/
class IsNthOrderThickening (n : ℕ) {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') : Prop extends IsFiniteOrderThickening i where
  /-- The `(n + 1)`st power of the associated ideal sheaf vanishes. -/
  pow_succ_eq_zero : (Hom.idealSheafSubobject i).pow_eq_bot (n + 1)

/-- A morphism of algebraic spaces is an `n`th-order thickening if and only if it
is a closed immersion whose associated ideal sheaf has vanishing `(n + 1)`st
power. -/
theorem isNthOrderThickening_iff (n : ℕ) {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} (i : X ⟶ X') :
    IsNthOrderThickening n i ↔
      IsClosedImmersion i ∧ (Hom.idealSheafSubobject i).pow_eq_bot (n + 1) :=
  sorry

namespace IsNthOrderThickening

/-- The identity morphism of an algebraic space is an `n`th-order thickening for
every `n`. -/
instance id (n : ℕ) {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsNthOrderThickening n (𝟙 X) :=
  sorry

/-- A `1`st-order thickening of algebraic spaces is a first-order thickening. -/
instance instIsFirstOrderThickening {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsNthOrderThickening 1 i] : IsFirstOrderThickening i :=
  sorry

end IsNthOrderThickening

namespace IsFirstOrderThickening

/-- A first-order thickening of algebraic spaces is a `1`st-order thickening. -/
instance instIsNthOrderThickening_one {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsFirstOrderThickening i] : IsNthOrderThickening 1 i :=
  sorry

end IsFirstOrderThickening

end AlgebraicGeometry.AlgebraicSpace
