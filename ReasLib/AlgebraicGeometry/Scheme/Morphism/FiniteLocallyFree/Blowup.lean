module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Blowup
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.DenseOpen
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations

/-!
# Finite locally free strict transforms

This module records the existence of admissible blowups whose strict transforms are finite
locally free.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A proper morphism over a quasi-compact quasi-separated scheme that is finite locally free
over a quasi-compact open has a finite locally free strict transform after an admissible blowup
away from that open. -/
theorem exists_isAdmissibleBlowup_finiteLocallyFree
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [IsProper f]
    (U : S.Opens) [QuasiCompact U.ι]
    [IsFiniteLocallyFree (f ∣_ U)] :
    ∃ (S' : Scheme.{u}) (b : S' ⟶ S) (I : S.IdealSheafData),
      IsAdmissibleBlowupCenter U b I ∧
        IsFiniteLocallyFree (strictTransformSnd b (I.comap b) f) := sorry

end AlgebraicGeometry.Scheme.Hom
