module

public import stacks_project.Chap87.«87_2_0_2_FormalScheme»

/-!
# Affine EGA formal schemes

An EGA formal scheme is affine when it is isomorphic, as a locally
topologically ringed space, to `Spf` of an admissible topological ring.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.FormalScheme

/-- The EGA affine formal scheme associated to the formal spectrum of an
admissible topological ring. -/
def ofSpf (A : TopCommRingCat.{u}) (hA : TopologicalRing.IsAdmissibleRing A) :
    FormalScheme.{u} where
  toLocallyTopologicallyRingedSpace := spf A hA
  local_affine := sorry

/-- The underlying locally topologically ringed space of `ofSpf A hA` is
`spf A hA`. -/
theorem ofSpf_toLocallyTopologicallyRingedSpace (A : TopCommRingCat.{u})
    (hA : TopologicalRing.IsAdmissibleRing A) :
    (ofSpf A hA).toLocallyTopologicallyRingedSpace = spf A hA :=
  sorry

/-- An EGA formal scheme is affine when it is isomorphic in LTRS to `Spf` of an
admissible topological ring. -/
class IsAffine (X : FormalScheme.{u}) : Prop where
  /-- There is an admissible topological ring whose formal spectrum is
  isomorphic to `X` in LTRS. -/
  exists_iso_spf :
    ∃ (A : TopCommRingCat.{u}) (hA : TopologicalRing.IsAdmissibleRing A),
      Nonempty (X.toLocallyTopologicallyRingedSpace ≅ spf A hA)

namespace IsAffine

/-- Exhibit an affine EGA formal scheme by an LTRS isomorphism to `spf A`. -/
theorem of {X : FormalScheme.{u}} {A : TopCommRingCat.{u}}
    (hA : TopologicalRing.IsAdmissibleRing A)
    (h : Nonempty (X.toLocallyTopologicallyRingedSpace ≅ spf A hA)) :
    IsAffine X :=
  sorry

/-- An affine EGA formal scheme is isomorphic in LTRS to `Spf` of an admissible
topological ring. -/
theorem spec (X : FormalScheme.{u}) [IsAffine X] :
    ∃ (A : TopCommRingCat.{u}) (hA : TopologicalRing.IsAdmissibleRing A),
      Nonempty (X.toLocallyTopologicallyRingedSpace ≅ spf A hA) :=
  sorry

/-- A formal scheme is affine iff it is isomorphic in LTRS to `Spf` of an
admissible topological ring. -/
theorem iff (X : FormalScheme.{u}) :
    IsAffine X ↔
      ∃ (A : TopCommRingCat.{u}) (hA : TopologicalRing.IsAdmissibleRing A),
        Nonempty (X.toLocallyTopologicallyRingedSpace ≅ spf A hA) :=
  sorry

end IsAffine

/-- `ofSpf A hA` is an affine EGA formal scheme. -/
instance instIsAffine_ofSpf (A : TopCommRingCat.{u})
    (hA : TopologicalRing.IsAdmissibleRing A) :
    IsAffine (ofSpf A hA) :=
  sorry

end AlgebraicGeometry.FormalScheme
