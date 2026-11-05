/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.KaehlerSquareZero
public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.MapsIntoAffineOpen
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Canonical infinitesimal automorphisms

The difference between pullback along the universal differential section and
pullback along the first-summand section is an infinitesimal automorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} (v : A ⟶ B)

/-- The differential section and the first-summand section have the same composite to the base ring's spectrum. -/
theorem specOverCan_comp_restrict :
    specOverCan v rfl ≫ specOverHom v rfl =
      specOverInl (Spec.map v ≫ σA) (CommRingCat.KaehlerDifferential v) ≫
        specOverHom v rfl := sorry

variable (x y : X.p.Fiber (Over.mk σA))

/-- The two restrictions of an object descending from the base ring are canonically isomorphic. -/
def canRestrictIso :
    Chosen.reindexObj X.p (specOverCan v rfl)
        (Chosen.reindexObj X.p (specOverHom v rfl) x) ≅
      trivialDeformation (Chosen.reindexObj X.p (specOverHom v rfl) x)
        (CommRingCat.KaehlerDifferential v) :=
  (Chosen.Reindex.specifiedCompIsoApp X.p (specOverHom v rfl) (specOverCan v rfl)
    (specOverInl (Spec.map v ≫ σA) (CommRingCat.KaehlerDifferential v) ≫
      specOverHom v rfl) (specOverCan_comp_restrict v) x).symm ≪≫
    Chosen.Reindex.specifiedCompIsoApp X.p (specOverHom v rfl)
      (specOverInl (Spec.map v ≫ σA) (CommRingCat.KaehlerDifferential v))
      (specOverInl (Spec.map v ≫ σA) (CommRingCat.KaehlerDifferential v) ≫
        specOverHom v rfl) rfl x

/-- The restriction identification is the composite of the inverse differential comparison and the inclusion comparison. -/
theorem canRestrictIso_hom :
    (canRestrictIso v x).hom =
      (Chosen.Reindex.specifiedCompIsoApp X.p (specOverHom v rfl) (specOverCan v rfl)
        (specOverInl (Spec.map v ≫ σA) (CommRingCat.KaehlerDifferential v) ≫
          specOverHom v rfl) (specOverCan_comp_restrict v) x).inv ≫
      (Chosen.Reindex.specifiedCompIsoApp X.p (specOverHom v rfl)
        (specOverInl (Spec.map v ≫ σA) (CommRingCat.KaehlerDifferential v))
        (specOverInl (Spec.map v ≫ σA) (CommRingCat.KaehlerDifferential v) ≫
          specOverHom v rfl) rfl x).hom := rfl

/-- Pullback along the differential section, transported to the trivial deformations. -/
def canHomOverTriv
    (α : Chosen.reindexObj X.p (specOverHom v rfl) x ⟶
      Chosen.reindexObj X.p (specOverHom v rfl) y) :
    trivialDeformation (Chosen.reindexObj X.p (specOverHom v rfl) x)
        (CommRingCat.KaehlerDifferential v) ⟶
      trivialDeformation (Chosen.reindexObj X.p (specOverHom v rfl) y)
        (CommRingCat.KaehlerDifferential v) :=
  (canRestrictIso v x).inv ≫ Chosen.reindexMap X.p (specOverCan v rfl) α ≫
    (canRestrictIso v y).hom

/-- The transported differential pullback is given by the canonical restriction identifications. -/
theorem canHomOverTriv_eq
    (α : Chosen.reindexObj X.p (specOverHom v rfl) x ⟶
      Chosen.reindexObj X.p (specOverHom v rfl) y) :
    canHomOverTriv v x y α =
      (canRestrictIso v x).inv ≫ Chosen.reindexMap X.p (specOverCan v rfl) α ≫
        (canRestrictIso v y).hom := rfl

/-- The difference of the differential pullback and the first-summand pullback as a fibre automorphism. -/
def canonicalAutArrow
    (α : Chosen.reindexObj X.p (specOverHom v rfl) x ⟶
      Chosen.reindexObj X.p (specOverHom v rfl) y) :
    Aut (trivialDeformation (Chosen.reindexObj X.p (specOverHom v rfl) x)
      (CommRingCat.KaehlerDifferential v)) :=
  { hom := canHomOverTriv v x y α
    inv := IsFibered.InGroupoids.fiberInverse _ (canHomOverTriv v x y α)
    hom_inv_id := IsFibered.InGroupoids.comp_fiberInverse _ _
    inv_hom_id := IsFibered.InGroupoids.fiberInverse_comp _ _ } ≪≫
    { hom := IsFibered.InGroupoids.fiberInverse _ (Chosen.reindexMap X.p
        (specOverInl (Spec.map v ≫ σA) (CommRingCat.KaehlerDifferential v)) α)
      inv := Chosen.reindexMap X.p
        (specOverInl (Spec.map v ≫ σA) (CommRingCat.KaehlerDifferential v)) α
      hom_inv_id := IsFibered.InGroupoids.fiberInverse_comp _ _
      inv_hom_id := IsFibered.InGroupoids.comp_fiberInverse _ _ }

/-- The difference automorphism composes the differential pullback with the inverse inclusion pullback. -/
theorem canonicalAutArrow_hom
    (α : Chosen.reindexObj X.p (specOverHom v rfl) x ⟶
      Chosen.reindexObj X.p (specOverHom v rfl) y) :
    (canonicalAutArrow v x y α).hom =
      canHomOverTriv v x y α ≫ inv (Chosen.reindexMap X.p
        (specOverInl (Spec.map v ≫ σA) (CommRingCat.KaehlerDifferential v)) α) := by
  exact congrArg (canHomOverTriv v x y α ≫ ·)
    (IsIso.eq_inv_of_hom_inv_id (IsFibered.InGroupoids.comp_fiberInverse _ _))

/-- The difference automorphism fixes the structural arrow of the trivial deformation lift. -/
theorem canonicalAut_restrict (h_mapsIntoAffineOpen : σA.MapsIntoAffineOpen)
    (α : Chosen.reindexObj X.p (specOverHom v rfl) x ⟶
      Chosen.reindexObj X.p (specOverHom v rfl) y) :
    (trivialDeformationLift (Chosen.reindexObj X.p (specOverHom v rfl) x)
        (CommRingCat.KaehlerDifferential v)).hom ≫
        Fiber.fiberInclusion.map (canonicalAutArrow v x y α).hom =
      (trivialDeformationLift (Chosen.reindexObj X.p (specOverHom v rfl) x)
        (CommRingCat.KaehlerDifferential v)).hom := sorry

/-- Over a locally Noetherian scheme, the two Kähler pullbacks of a fibre morphism determine an infinitesimal automorphism of its source. -/
def canonicalAut [HasStrongRimSchlessinger X] [IsLocallyNoetherian S]
    (h_mapsIntoAffineOpen : σA.MapsIntoAffineOpen)
    (α : Chosen.reindexObj X.p (specOverHom v rfl) x ⟶
      Chosen.reindexObj X.p (specOverHom v rfl) y) :
    (infFunctor (Chosen.reindexObj X.p (specOverHom v rfl) x)).obj
      (CommRingCat.KaehlerDifferential v) :=
  ⟨canonicalAutArrow v x y α, canonicalAut_restrict v x y h_mapsIntoAffineOpen α⟩

/-- The underlying automorphism of the canonical infinitesimal automorphism is the difference of the two pullbacks. -/
theorem canonicalAut_val [HasStrongRimSchlessinger X] [IsLocallyNoetherian S]
    (h_mapsIntoAffineOpen : σA.MapsIntoAffineOpen)
    (α : Chosen.reindexObj X.p (specOverHom v rfl) x ⟶
      Chosen.reindexObj X.p (specOverHom v rfl) y) :
    (canonicalAut v x y h_mapsIntoAffineOpen α).val = canonicalAutArrow v x y α := rfl

/-- Left composition of the inclusion pullback with the difference automorphism recovers the differential pullback. -/
theorem canonicalAut_spec (h_mapsIntoAffineOpen : σA.MapsIntoAffineOpen)
    (α : Chosen.reindexObj X.p (specOverHom v rfl) x ⟶
      Chosen.reindexObj X.p (specOverHom v rfl) y) :
    (canonicalAutArrow v x y α).hom ≫ Chosen.reindexMap X.p
        (specOverInl (Spec.map v ≫ σA) (CommRingCat.KaehlerDifferential v)) α =
      canHomOverTriv v x y α := by
  rw [canonicalAutArrow_hom]
  exact (Category.assoc _ _ _).trans
    ((congrArg (canHomOverTriv v x y α ≫ ·) (IsIso.inv_hom_id _)).trans
      (Category.comp_id _))

/-- The canonical infinitesimal automorphism of an identity morphism is zero. -/
theorem canonicalAut_id [HasStrongRimSchlessinger X] [IsLocallyNoetherian S]
    (h_mapsIntoAffineOpen : σA.MapsIntoAffineOpen) :
    canonicalAut v x x h_mapsIntoAffineOpen
      (𝟙 (Chosen.reindexObj X.p (specOverHom v rfl) x)) = 0 := sorry

end AlgebraicGeometry.GroupoidsOver
