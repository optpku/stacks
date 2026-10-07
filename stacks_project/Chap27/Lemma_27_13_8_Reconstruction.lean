module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
public import stacks_project.Chap27.Lemma_27_13_8_TwistedSections

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.TwistedSections

variable {R : Type u} [CommRing R] {n : ℕ}

/-- Restriction of module sheaves on projective space to the coordinate chart `D₊(T_i)`. -/
noncomputable abbrev coordinateRestrict (R : Type u) [CommRing R]
    (n : ℕ) (i : Fin (n + 1)) :=
  Scheme.Modules.restrictFunctor
    ((ProjectiveSpace.coordinateBasicOpen n i : (ProjectiveSpace.scheme R n).affineOpens).1.ι)

/-- Explicit coordinate-chart data for the reconstruction comparison: a concrete global
morphism together with isomorphisms identifying each of its restrictions to `D₊(T_i)`. -/
structure CoordinateTrivialization.{v} {R : Type v} [CommRing R] {n : ℕ}
    (P : ProjTwistPresentation (ProjectiveSpace.grading R n))
    (T : ProjTwistMulPresentation (ProjectiveSpace.grading R n) P) where
  /-- The comparison from the sheaf associated to the nonnegative twisted-section sum to `F`. -/
  hom : ∀ F : Scheme.QCoh (ProjectiveSpace.scheme R n),
    associatedSheaf P T F ⟶
      (Scheme.QCoh.inclusion (ProjectiveSpace.scheme R n)).obj F
  /-- The comparison isomorphism on each standard coordinate chart. -/
  chartIso : ∀ (F : Scheme.QCoh (ProjectiveSpace.scheme R n)) (i : Fin (n + 1)),
    (coordinateRestrict R n i).obj (associatedSheaf P T F) ≅
      (coordinateRestrict R n i).obj
        ((Scheme.QCoh.inclusion (ProjectiveSpace.scheme R n)).obj F)
  /-- Restricting the global comparison to `D₊(T_i)` gives the chosen coordinate isomorphism. -/
  hom_coordinate : ∀ (F : Scheme.QCoh (ProjectiveSpace.scheme R n)) (i : Fin (n + 1)),
    (coordinateRestrict R n i).map (hom F) = (chartIso F i).hom

/-- Construct coordinate reconstruction data from an explicit comparison, its chart
isomorphisms, and the chartwise comparison formula. -/
def CoordinateTrivialization.of
    (P : ProjTwistPresentation (ProjectiveSpace.grading R n))
    (T : ProjTwistMulPresentation (ProjectiveSpace.grading R n) P)
    (hom : ∀ F : Scheme.QCoh (ProjectiveSpace.scheme R n),
      associatedSheaf P T F ⟶
        (Scheme.QCoh.inclusion (ProjectiveSpace.scheme R n)).obj F)
    (chartIso : ∀ (F : Scheme.QCoh (ProjectiveSpace.scheme R n)) (i : Fin (n + 1)),
      (coordinateRestrict R n i).obj (associatedSheaf P T F) ≅
        (coordinateRestrict R n i).obj
          ((Scheme.QCoh.inclusion (ProjectiveSpace.scheme R n)).obj F))
    (hom_coordinate : ∀ (F : Scheme.QCoh (ProjectiveSpace.scheme R n))
      (i : Fin (n + 1)),
      (coordinateRestrict R n i).map (hom F) = (chartIso F i).hom) :
    CoordinateTrivialization P T :=
  ⟨hom, chartIso, hom_coordinate⟩

/-- The coordinate-trivialization specification simultaneously exposes the restricted
comparison and its chartwise isomorphism. -/
theorem CoordinateTrivialization.spec
    (P : ProjTwistPresentation (ProjectiveSpace.grading R n))
    (T : ProjTwistMulPresentation (ProjectiveSpace.grading R n) P)
    (C : CoordinateTrivialization P T)
    (F : Scheme.QCoh (ProjectiveSpace.scheme R n)) (i : Fin (n + 1)) :
    (coordinateRestrict R n i).map (C.hom F) = (C.chartIso F i).hom := sorry

/-- The canonical comparison determined by the chosen coordinate reconstruction data. -/
def reconstructionHom
    (P : ProjTwistPresentation (ProjectiveSpace.grading R n))
    (T : ProjTwistMulPresentation (ProjectiveSpace.grading R n) P)
    (C : CoordinateTrivialization P T)
    (F : Scheme.QCoh (ProjectiveSpace.scheme R n)) :
    associatedSheaf P T F ⟶
      (Scheme.QCoh.inclusion (ProjectiveSpace.scheme R n)).obj F :=
  C.hom F

/-- On `D₊(T_i)`, `reconstructionHom` is the chosen coordinate comparison isomorphism; this is
the formal chartwise version of the fraction formula `m / T_i ^ d ↦ m_i`. -/
theorem reconstructionHom_coordinate
    (P : ProjTwistPresentation (ProjectiveSpace.grading R n))
    (T : ProjTwistMulPresentation (ProjectiveSpace.grading R n) P)
    (C : CoordinateTrivialization P T)
    (F : Scheme.QCoh (ProjectiveSpace.scheme R n)) (i : Fin (n + 1)) :
    (coordinateRestrict R n i).map (reconstructionHom P T C F) =
      (C.chartIso F i).hom := sorry

end AlgebraicGeometry.ProjectiveSpace.TwistedSections
