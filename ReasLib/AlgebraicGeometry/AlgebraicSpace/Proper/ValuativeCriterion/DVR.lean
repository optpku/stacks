module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dominant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Factorization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.ValuativeCriterion.DVR

/-!
# Refined Noetherian DVR valuative criterion for properness

A finite-type separated morphism of algebraic spaces into a locally Noetherian
target is proper if factored DVR valuative squares along a dense finite-type
morphism admit dotted lifts.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion.DVR.Along

/-- A separated finite-type morphism to a locally Noetherian algebraic space is
proper if every DVR valuative square whose generic arrow factors through a
dense finite-type morphism admits a dotted lift over the original DVR. -/
theorem proper_of_separated {S : Scheme.{u}} {U X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (h : U ⟶ X) [IsLocallyNoetherian Y] [FiniteType f]
    [FiniteType h] [Separated f] [Dominant h]
    (h_existence : Existence h f) : Proper f :=
  sorry

/-- A finite-type quasi-separated morphism to a locally Noetherian algebraic
space is proper if every DVR valuative square whose generic arrow factors
through a dense finite-type morphism admits a unique dotted lift over the
original DVR. -/
theorem proper {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (h : U ⟶ X) [IsLocallyNoetherian Y] [FiniteType f] [FiniteType h]
    [QuasiSeparated f] [Dominant h] (h_valuative : ExistsUnique h f) :
    Proper f :=
  sorry

end ValuativeCriterion.DVR.Along

end AlgebraicGeometry.AlgebraicSpace
