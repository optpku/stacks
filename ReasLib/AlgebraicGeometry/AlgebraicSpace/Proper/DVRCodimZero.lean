module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.ValuativeCriterion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.CodimZero

/-!
# Noetherian DVR valuative criterion for properness

For a quasi-separated finite-type morphism into a locally Noetherian algebraic
space, properness is equivalent to unique lifting for DVR valuative squares,
even when testing only squares whose generic image has codimension zero.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Proper

/-- For a quasi-separated finite-type morphism into a locally Noetherian algebraic
space, properness, the valuative criterion, unique lifting for all valuative
squares, unique lifting for DVR squares, and unique lifting for DVR squares whose
generic image has codimension zero are equivalent. -/
@[stacks 0H1X]
theorem tfae_valuativeCriterion_dvr_codimZero {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiSeparated f] [FiniteType f] [IsLocallyNoetherian Y] :
    List.TFAE [Proper f, ValuativeCriterion f,
      ∀ sq : ValuativeCommSq f, sq.commSq.HasLift ∧ Subsingleton sq.commSq.LiftStruct,
      ValuativeCriterion.DVR f, ValuativeCriterion.DVR.AtCodimZero f] :=
  sorry

/-- A quasi-separated, finite-type morphism into a locally Noetherian algebraic space
is proper if and only if every DVR valuative square has a unique lift. -/
theorem iff_dvr {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiSeparated f] [FiniteType f] [IsLocallyNoetherian Y] :
    Proper f ↔ ValuativeCriterion.DVR f :=
  (tfae_valuativeCriterion_dvr_codimZero f).out 0 3

/-- A quasi-separated, finite-type morphism into a locally Noetherian algebraic space
is proper if and only if every DVR valuative square whose generic image has
codimension `0` has a unique lift. -/
theorem iff_dvrAtCodimZero {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiSeparated f] [FiniteType f] [IsLocallyNoetherian Y] :
    Proper f ↔ ValuativeCriterion.DVR.AtCodimZero f :=
  (tfae_valuativeCriterion_dvr_codimZero f).out 0 4

/-- A quasi-separated, finite-type morphism into a locally Noetherian algebraic space
that satisfies unique DVR lifts at codimension-zero points is proper. -/
instance of_dvrAtCodimZero {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiSeparated f] [FiniteType f] [IsLocallyNoetherian Y]
    [ValuativeCriterion.DVR.AtCodimZero f] : Proper f :=
  (iff_dvrAtCodimZero f).mpr inferInstance

end Proper

end AlgebraicGeometry.AlgebraicSpace
