module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Noetherian valuative squares

Valuative squares arising from finite-type morphisms over locally Noetherian schemes may have a
discrete valuation ring as their valuation ring, except that a trivial specialization naturally
produces a field. This file packages both cases without enlarging the generic residue field.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A valuative square whose generic map is the residue-field map of a generic point and whose
valuation subring is either a discrete valuation ring or a field. -/
structure DvrOrFieldValuativeCommSqAt {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- The generic point that determines the generic map. -/
  sourcePoint : X
  /-- The source point is generic in an irreducible component of the source scheme. -/
  sourcePoint_mem : sourcePoint ∈ genericPoints X
  /-- The valuation subring of the residue field of the source point. -/
  V : ValuationSubring (X.residueField sourcePoint)
  /-- The valuation subring is a discrete valuation ring or is the whole generic field. -/
  dvrOrField : IsDiscreteValuationRing V ∨ IsField V
  /-- The map from the spectrum of the valuation subring to the target scheme. -/
  toTarget : Spec (CommRingCat.of V) ⟶ Y
  /-- The generic residue-field map and the valuation-spectrum map form a commutative square. -/
  commSq : CommSq (X.fromSpecResidueField sourcePoint)
    (Spec.map (CommRingCat.ofHom (algebraMap V (X.residueField sourcePoint)))) f toTarget

namespace DvrOrFieldValuativeCommSqAt

/-- Forget the distinguished generic point and the DVR-or-field alternative, retaining the
underlying valuative square. -/
noncomputable def toValuativeCommSq {X Y : Scheme.{u}} {f : X ⟶ Y}
    (sq : DvrOrFieldValuativeCommSqAt f) : ValuativeCommSq f where
  R := sq.V
  K := X.residueField sq.sourcePoint
  i₁ := X.fromSpecResidueField sq.sourcePoint
  i₂ := sq.toTarget
  commSq := sq.commSq

/-- The image in the target of the closed point of the valuation subring. -/
noncomputable def closedPointImage {X Y : Scheme.{u}} {f : X ⟶ Y}
    (sq : DvrOrFieldValuativeCommSqAt f) : Y :=
  sq.toTarget (IsLocalRing.closedPoint sq.V)

/-- A DVR-or-field valuative square records generic-point membership, the DVR-or-field
alternative, and the commutativity of its underlying square. -/
theorem spec {X Y : Scheme.{u}} {f : X ⟶ Y} (sq : DvrOrFieldValuativeCommSqAt f) :
    sq.sourcePoint ∈ genericPoints X ∧
      (IsDiscreteValuationRing sq.V ∨ IsField sq.V) ∧
        CommSq (X.fromSpecResidueField sq.sourcePoint)
          (Spec.map (CommRingCat.ofHom
            (algebraMap sq.V (X.residueField sq.sourcePoint)))) f sq.toTarget := sorry

end DvrOrFieldValuativeCommSqAt

namespace Scheme.Hom

/-- For a finite-type morphism to a locally Noetherian scheme, every point in the closure of the
image is the closed-point image of a DVR-or-field valuative square based at a generic point of the
source. -/
@[stacks 0CM2]
theorem exists_dvrOrFieldValuativeCommSqAt_of_mem_closure_range
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Scheme.Hom.FiniteType f] [IsLocallyNoetherian Y]
    {y : Y} (hy : y ∈ closure (Set.range f.base)) :
    ∃ sq : DvrOrFieldValuativeCommSqAt f, sq.closedPointImage = y := sorry

end Scheme.Hom
end AlgebraicGeometry
