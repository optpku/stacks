/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Definition
public import ReasLib.Topology.Sheaf.Indiscrete
public import ReasLib.Topology.Sheaves.Skyscraper
public import Mathlib.Tactic.CrossRefAttribute

/-!
# One-point ringed spaces

This module constructs the ringed point attached to an arbitrary commutative ring.  It also owns
the morphism from a ringed space to that point classified by a homomorphism from the coefficient
ring to global sections.  Module sheaves on a ringed point are treated in
`AlgebraicGeometry.RingedSpace.Module.Point`.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedPoint

/-- The underlying one-point topological space used by `RingedPoint.of`. -/
abbrev carrier : TopCat := TopCat.of PUnit

/-- The unique point of `RingedPoint.carrier`. -/
abbrev point : carrier := PUnit.unit

/-- The structure sheaf on a ringed point with coefficient ring `R`. -/
noncomputable abbrev structureSheaf (R : Type u) [CommRing R] :
    TopCat.Sheaf CommRingCat carrier :=
  TopCat.Sheaf.Skyscraper.atPoint point (CommRingCat.of R)

/-- The one-point ringed space whose ring on the unique nonempty open is `R`. -/
@[stacks 01BH "one-point ringed space"]
noncomputable abbrev of (R : Type u) [CommRing R] : RingedSpace where
  carrier := carrier
  presheaf := (structureSheaf R).obj
  IsSheaf := (structureSheaf R).property

/-- A ringed point has the indiscrete topology. -/
instance of_indiscreteTopology (R : Type u) [CommRing R] :
    IndiscreteTopology (of R) := inferInstance

/-- The `RingCat`-valued structure sheaf of a ringed point. -/
noncomputable abbrev ringCatSheaf (R : Type u) [CommRing R] :=
  RingedSpace.ringCatSheaf (of R)

/-- The structure ring on the top open of `RingedPoint.of R` is `R`. -/
theorem ringCatSheaf_obj_top (R : Type u) [CommRing R] :
    (ringCatSheaf R).obj.obj (op (⊤ : Opens carrier)) = RingCat.of R := sorry

/-- The commutative-ring-valued structure sheaf on the top open of `RingedPoint.of R` is `R`. -/
theorem presheaf_obj_top (R : Type u) [CommRing R] :
    (of R).presheaf.obj (op (⊤ : Opens carrier)) = CommRingCat.of R := sorry

/-- The canonical identification of the top-open structure ring with the coefficient ring. -/
noncomputable def topRingIso (R : Type u) [CommRing R] :
    (ringCatSheaf R).obj.obj (op (⊤ : Opens carrier)) ≅ RingCat.of R :=
  eqToIso (by
    let pointSheaf : TopCat.Sheaf CommRingCat carrier := structureSheaf R
    change (forget₂ CommRingCat RingCat).obj (pointSheaf.obj.obj (op ⊤)) = RingCat.of R
    simp [pointSheaf, skyscraperSheaf, skyscraperPresheaf]
    rfl)

/-- The canonical commutative-ring identification of the top-open value with the coefficient
ring. -/
noncomputable def topCommRingIso (R : Type u) [CommRing R] :
    (of R).presheaf.obj (op (⊤ : Opens carrier)) ≅ CommRingCat.of R :=
  eqToIso (by
    let pointSheaf : TopCat.Sheaf CommRingCat carrier := structureSheaf R
    change pointSheaf.obj.obj (op ⊤) = CommRingCat.of R
    simp [pointSheaf, skyscraperSheaf, skyscraperPresheaf])

/-- The unique stalk of a ringed point is canonically its coefficient ring. -/
noncomputable def stalkIso (R : Type u) [CommRing R] :
    (of R).presheaf.stalk point ≅ CommRingCat.of R :=
  TopCat.Sheaf.Skyscraper.stalkIsoOfSpecializes point (CommRingCat.of R)
    (specializes_rfl : point ⤳ point)

/-- The unique continuous map from a topological space to the underlying space of a ringed
point. -/
abbrev baseMap (X : TopCat.{u}) : X ⟶ carrier :=
  ofHom (ContinuousMap.const X point)

/-- Pushing a sheaf forward along the unique map to the point and evaluating at the top open
recovers its top-open value. -/
noncomputable def pushforwardTopIso (X : RingedSpace.{u}) :
    ((TopCat.Sheaf.pushforward CommRingCat (baseMap X)).obj X.sheaf).obj.obj
        (op (⊤ : Opens carrier)) ≅
      X.presheaf.obj (op (⊤ : Opens X)) :=
  eqToIso (by
    change
      X.presheaf.obj (op ((Opens.map (baseMap X)).obj (⊤ : Opens carrier))) =
        X.presheaf.obj (op (⊤ : Opens X))
    rw [show (Opens.map (baseMap X)).obj (⊤ : Opens carrier) =
      (⊤ : Opens X) by
      ext x
      simp [baseMap]])

/-- The map on top-open structure rings underlying the morphism to a ringed point classified by
`alpha : R →+* Γ(X, O_X)`. -/
noncomputable def structureMapTop {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (alpha : R →+* X.presheaf.obj (op ⊤)) :
    (of R).presheaf.obj (op (⊤ : Opens carrier)) ⟶
      ((baseMap X) _* X.presheaf).obj (op ⊤) :=
  (topCommRingIso R).hom ≫ CommRingCat.ofHom alpha ≫ (pushforwardTopIso X).inv

/-- The structure-sheaf morphism underlying the map to a ringed point classified by a map into
global sections. -/
@[stacks 01BH "structure map to a ringed point"]
noncomputable def structureMap {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (alpha : R →+* X.presheaf.obj (op ⊤)) :
    (of R).presheaf ⟶ (baseMap X) _* X.presheaf :=
  (TopCat.Sheaf.Indiscrete.homOfTop (structureSheaf R)
    ((TopCat.Sheaf.pushforward CommRingCat (baseMap X)).obj X.sheaf)
    (structureMapTop alpha)).hom

/-- The morphism `X ⟶ RingedPoint.of R` classified by
`alpha : R →+* Γ(X, O_X)`. -/
@[stacks 01BH "morphism classified by a map to global sections"]
noncomputable def fromGlobalSections {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (alpha : R →+* X.presheaf.obj (op ⊤)) : X ⟶ of R :=
  InducedCategory.homMk
    { base := baseMap X
      c := structureMap alpha }

/-- The underlying continuous map of `fromGlobalSections alpha` is the unique map to the point. -/
@[simp]
theorem fromGlobalSections_base {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (alpha : R →+* X.presheaf.obj (op ⊤)) :
    (fromGlobalSections alpha).hom.base = baseMap X := sorry

/-- The structure map of `fromGlobalSections alpha` on the top open is `alpha`. -/
@[simp]
theorem fromGlobalSections_app_top {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (alpha : R →+* X.presheaf.obj (op ⊤)) :
    (fromGlobalSections alpha).hom.c.app (op ⊤) = structureMapTop alpha := sorry

end AlgebraicGeometry.RingedPoint
