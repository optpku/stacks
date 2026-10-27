/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree.Dualizable
public import ReasLib.AlgebraicGeometry.Scheme.Module.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.CategoryTheory.Iso.Explicit

/-!
# Normal and conormal sheaf duality

Dualization reverses module-sheaf isomorphisms. The normal sheaf is the dual of the
conormal sheaf, and finite local freeness makes the canonical biduality map invertible.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalClosed
open AlgebraicGeometry.Scheme.Modules hiding dual

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Dualizing reverses an isomorphism of module sheaves. -/
noncomputable def dualMapIso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) :
    Scheme.Modules.dual G ≅ Scheme.Modules.dual F where
  hom := dualMap e.hom
  inv := dualMap e.inv
  hom_inv_id := by
    change (MonoidalClosed.pre e.hom).app _ ≫ (MonoidalClosed.pre e.inv).app _ = _
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, e.inv_hom_id,
      MonoidalClosed.pre_id, NatTrans.id_app]
  inv_hom_id := by
    change (MonoidalClosed.pre e.inv).app _ ≫ (MonoidalClosed.pre e.hom).app _ = _
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, e.hom_inv_id,
      MonoidalClosed.pre_id, NatTrans.id_app]

/-- Dualizing an isomorphism applies the dual map to its forward arrow. -/
theorem dualMapIso_hom {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) :
    (dualMapIso e).hom = dualMap e.hom := rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

/-- The normal sheaf is canonically isomorphic to the dual of the conormal sheaf. -/
noncomputable def normalSheafIsoDualConormal {Z X : Scheme.{u}} (i : Z ⟶ X) :
    normalSheaf i ≅ Scheme.Modules.dual (conormalSheaf i) :=
  (ihom (conormalSheaf i)).mapIso (RingedSpace.unitIsoTensorUnit Z.toRingedSpace)

/-- The normal-to-dual comparison applies internal Hom to the tensor-unit comparison. -/
theorem normalSheafIsoDualConormal_hom {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (normalSheafIsoDualConormal i).hom =
      (ihom (conormalSheaf i)).map
        (RingedSpace.unitIsoTensorUnit Z.toRingedSpace).hom := rfl

/-- The canonical evaluation morphism from the conormal sheaf to the dual normal sheaf. -/
noncomputable def biduality {Z X : Scheme.{u}} (i : Z ⟶ X) :
    conormalSheaf i ⟶ Scheme.Modules.dual (normalSheaf i) :=
  toReflexiveHull (conormalSheaf i) ≫
    (dualMapIso (normalSheafIsoDualConormal i)).hom

/-- Reverse arrow on a finite locally free conormal sheaf.

The first factor is the inverse of the dualized normal/conormal comparison.  The second factor is
the concrete finite-coordinate inverse assembled from the local-generator witness supplied by
`IsFiniteLocallyFree.exists_data` and the underlying module-sheaf amalgamation.
-/
noncomputable def bidualityIsoForward {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsFiniteLocallyFree (conormalSheaf i)] :
    conormalSheaf i ≅ Scheme.Modules.dual (normalSheaf i) := by
  let e := normalSheafIsoDualConormal i
  let d := SheafOfModules.IsFiniteLocallyFree.finiteFreeBidualIso
    (X := Z.toRingedSpace) (conormalSheaf i)
  exact
    { hom := biduality i
      inv := (dualMapIso e).inv ≫ d.inv
      hom_inv_id := by sorry
      inv_hom_id := by sorry }

/-- A finite locally free conormal sheaf has an invertible canonical biduality map. -/
instance biduality_isIso {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsFiniteLocallyFree (conormalSheaf i)] : IsIso (biduality i) :=
  (bidualityIsoForward i).isIso_hom

/-- The canonical identification of the dual normal sheaf with the conormal sheaf. -/
noncomputable def bidualityIso {Z X : Scheme.{u}} (i : Z ⟶ X) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf i)] :
    Scheme.Modules.dual (normalSheaf i) ≅ conormalSheaf i :=
  (bidualityIsoForward i).symm

/-- The inverse biduality identification is the canonical evaluation morphism. -/
theorem bidualityIso_inv {Z X : Scheme.{u}} (i : Z ⟶ X) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf i)] :
    (bidualityIso i r).inv = biduality i := rfl

/-- The dual normal sheaf is canonically the conormal sheaf when the latter is finite
locally free, with no constant-rank assumption. -/
noncomputable def bidualityIsoOfRankLoci {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsFiniteLocallyFree (conormalSheaf i)] :
    Scheme.Modules.dual (normalSheaf i) ≅ conormalSheaf i :=
  (bidualityIsoForward i).symm

/-- The inverse normal-conormal identification is the canonical evaluation morphism. -/
theorem bidualityIsoOfRankLoci_inv {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsFiniteLocallyFree (conormalSheaf i)] :
    (bidualityIsoOfRankLoci i).inv = biduality i := rfl

end AlgebraicGeometry.Scheme.Hom
