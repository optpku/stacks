/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorPower.Multiplication

/-!
# Comparisons for tensor powers of module sheaves

This leaf owns the canonical recursive comparisons between nonnegative tensor powers. It is
independent of global sections, invertibility, and graded constructions. The canonical names live
in `RingedSpace.TensorPower`; the former root names are deprecated compatibility aliases.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.TensorPower

variable {X : RingedSpace.{u}}

/-- An isomorphism of module sheaves induces canonical isomorphisms on all nonnegative tensor
powers. -/
@[stacks 01CK "isomorphism of ringed-space tensor powers"]
noncomputable abbrev mapIso {L L' : X.Modules} (e : L ≅ L') (n : ℕ) :
    sheaf L n ≅ sheaf L' n :=
  (functor X n).mapIso e

/-- Transport a module-sheaf isomorphism across the canonical degree-one tensor-power
identifications. -/
@[stacks 01CK "transport across first tensor powers"]
noncomputable def oneIsoCongr {L L' : X.Modules} (e : L ≅ L') :
    sheaf L 1 ≅ sheaf L' 1 :=
  oneIso L ≪≫ e ≪≫ (oneIso L').symm

/-- The canonical rebracketing
`TensorPower.sheaf (TensorPower.sheaf L a) m ≅ TensorPower.sheaf L (m * a)`. -/
@[stacks 01CK "multiplication of tensor-power degrees"]
noncomputable def mulIso (L : X.Modules) :
    (a m : ℕ) → sheaf (sheaf L a) m ≅ sheaf L (m * a)
  | a, 0 =>
      eqToIso (congrArg (sheaf L) (Nat.zero_mul a)).symm
  | a, m + 1 =>
      (Iso.refl _ ⊗ᵢ mulIso L a m) ≪≫
        addIso L a (m * a) ≪≫
          eqToIso
            (congrArg (sheaf L)
              ((Nat.add_comm a (m * a)).trans (Nat.succ_mul m a).symm))

end AlgebraicGeometry.RingedSpace.TensorPower

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- Compatibility name for `TensorPower.mapIso`. -/
@[stacks 01CK "compatibility name for ringed-space tensor-power maps",
  deprecated TensorPower.mapIso (since := "2026-08-04")]
noncomputable abbrev tensorPowerSheaf_mapIso {L L' : X.Modules} (e : L ≅ L') :
    (n : ℕ) → TensorPower.sheaf L n ≅ TensorPower.sheaf L' n :=
  TensorPower.mapIso e

/-- Compatibility name for `TensorPower.oneIsoCongr`. -/
@[stacks 01CK "compatibility name for first tensor-power transport",
  deprecated TensorPower.oneIsoCongr (since := "2026-08-04")]
noncomputable abbrev tensorPowerSheaf_oneIso_congr {L L' : X.Modules} (e : L ≅ L') :
    TensorPower.sheaf L 1 ≅ TensorPower.sheaf L' 1 :=
  TensorPower.oneIsoCongr e

/-- Compatibility name for `TensorPower.mulIso`. -/
@[stacks 01CK "compatibility name for tensor-power degree multiplication",
  deprecated TensorPower.mulIso (since := "2026-08-04")]
noncomputable abbrev tensorPowerSheaf_mulIso (L : X.Modules) :
    (a m : ℕ) → TensorPower.sheaf (TensorPower.sheaf L a) m ≅
      TensorPower.sheaf L (m * a) :=
  TensorPower.mulIso L

end AlgebraicGeometry.RingedSpace


