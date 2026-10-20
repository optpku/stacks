module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Admissible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

/-!
# Domination of proper modifications of algebraic spaces by admissible blowups

A proper morphism of algebraic spaces that is an isomorphism over a
quasi-compact open of a qcqs base is dominated by a `U`-admissible blowup.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper morphism of algebraic spaces that is an isomorphism over a
quasi-compact open of a quasi-compact, quasi-separated base is dominated by
an admissible blowup away from that open. -/
theorem exists_isAdmissibleBlowup_dominating
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiCompact B] [IsAbsolutelyQuasiSeparated B]
    (f : X ⟶ B) [Proper f]
    (U : OpenSubspace B) [IsQuasiCompact U.X]
    [IsIso (pullback.snd f U.ι)] :
    ∃ (B' : AlgebraicSpace S) (b : B' ⟶ B) (g : B' ⟶ X),
      IsAdmissibleBlowup U b ∧ g ≫ f = b :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
