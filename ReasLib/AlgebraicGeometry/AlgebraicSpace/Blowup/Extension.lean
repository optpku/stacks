module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Admissible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Intersection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Extension of admissible blowups of algebraic spaces

An admissible blowup of a quasi-compact open subspace extends to the whole
quasi-compact quasi-separated algebraic space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An admissible blowup of a quasi-compact open subspace of a quasi-compact
quasi-separated algebraic space extends to an admissible blowup of the whole space
whose center avoids a prescribed quasi-compact open, with the original blowup
recovered by restriction. -/
theorem exists_isAdmissibleBlowup_restrict_iso_of_isAdmissibleBlowup_inter
    {S : Scheme.{u}} {X V' : AlgebraicSpace S} [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (U V : OpenSubspace X)
    [QuasiCompact U.ι] [QuasiCompact V.ι] (b : V' ⟶ V.X)
    (hb : IsAdmissibleBlowup (U.preimage V) b) :
    ∃ (X' : AlgebraicSpace S) (π : X' ⟶ X),
      IsAdmissibleBlowup U π ∧ Nonempty (Over.mk (pullback.snd π V.ι) ≅ Over.mk b) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
