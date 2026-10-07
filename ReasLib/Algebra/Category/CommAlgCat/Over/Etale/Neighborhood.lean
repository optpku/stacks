module

public import ReasLib.Algebra.Category.CommAlgCat.Over.Etale
public import ReasLib.RingTheory.Etale.Neighborhood.Localization
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pointed etale over-objects as neighborhoods

The category `CommAlgCat.Over.Etale.category R κ(p)` is a convenient
source-facing presentation.  The reusable geometric owner is
`PrimeSpectrum.EtaleNeighborhood p`; this leaf supplies the bridge between
the two presentations without introducing a second category or hiding the
selected point.  Ring-level localization data remains under
`PrimeSpectrum.EtaleNeighborhood`; the bundled `CommAlgCat` localization
object is placed here because it is the only part requiring a category.

@stack 04GV
-/

universe u v

namespace CommAlgCat.Over.Etale

/-- The point selected by an object over `κ(p)` is the kernel of its map to
the residue field. -/
@[stacks 04GV "selected point of a pointed etale algebra"]
noncomputable def selectedPoint
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    (A : category R p.asIdeal.ResidueField) : PrimeSpectrum A.obj.left :=
  ⟨RingHom.ker A.obj.hom.hom.toRingHom, RingHom.ker_isPrime _⟩

/-- The selected point of a pointed etale over-object lies over the base
point. -/
@[stacks 04GV "lying-over equation for a pointed etale algebra"]
theorem selectedPoint_over
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    (A : category R p.asIdeal.ResidueField) :
    p.asIdeal = Ideal.comap (algebraMap R A.obj.left) (selectedPoint p A).asIdeal := sorry

/-- The selected point has the same residue field as the base point. -/
@[stacks 04GV "residue-field bijectivity of a pointed etale algebra"]
theorem selectedPoint_residueField_bijective
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    (A : category R p.asIdeal.ResidueField) :
    Function.Bijective
      (Ideal.ResidueField.map p.asIdeal (selectedPoint p A).asIdeal
        (algebraMap R A.obj.left) (selectedPoint_over p A)) := sorry

/-- Convert a pointed etale over-object into the canonical bundled
neighborhood owner. -/
@[stacks 04GV "pointed etale algebra to etale neighborhood"]
noncomputable def toNeighborhood
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    (A : category R p.asIdeal.ResidueField) :
    PrimeSpectrum.EtaleNeighborhood.{u, u} p :=
  letI : Algebra.Etale R A.obj.left :=
    (RingHom.etale_algebraMap (R := R) (S := A.obj.left)).mp A.property
  PrimeSpectrum.EtaleNeighborhood.of (selectedPoint p A)
    (selectedPoint_over p A) (selectedPoint_residueField_bijective p A)

/-- The bridge preserves the carrier by construction. -/
@[simp, stacks 04GV "carrier of a pointed etale neighborhood"]
theorem toNeighborhood_carrier
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    (A : category R p.asIdeal.ResidueField) :
    (toNeighborhood p A).carrier = A.obj.left := sorry

/-- The bridge preserves the selected point by construction. -/
@[simp, stacks 04GV "point of a pointed etale neighborhood"]
theorem toNeighborhood_selectedPoint
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    (A : category R p.asIdeal.ResidueField) :
    (toNeighborhood p A).point = selectedPoint p A := sorry

/-- The carrier and selected point of the bridge are its defining data. -/
@[stacks 04GV "specification of a pointed etale neighborhood"]
theorem toNeighborhood_spec
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    (A : category R p.asIdeal.ResidueField) :
    (toNeighborhood p A).carrier = A.obj.left ∧
      (toNeighborhood p A).point = selectedPoint p A := sorry

end CommAlgCat.Over.Etale

namespace PrimeSpectrum.EtaleNeighborhood

/-- The localization of an etale neighborhood as a commutative algebra over
`Rₚ`.  This categorical wrapper uses the named, non-global ring-level
`U.localizationAlgebra`, so the scalar choice remains explicit at the
category boundary. -/
@[stacks 04GV "localized etale-neighborhood algebra object"]
noncomputable def localizationObject
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtaleNeighborhood.{u, v} p) :
    CommAlgCat (Localization.AtPrime p.asIdeal) := by
  letI : Algebra (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime U.point.asIdeal) := U.localizationAlgebra
  exact CommAlgCat.of (Localization.AtPrime p.asIdeal)
    (Localization.AtPrime U.point.asIdeal)

end PrimeSpectrum.EtaleNeighborhood
