module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
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

/-- A finite locally free conormal sheaf has an invertible canonical biduality map. -/
instance biduality_isIso {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsFiniteLocallyFree (conormalSheaf i)] : IsIso (biduality i) := sorry

/-- The canonical identification of the dual normal sheaf with the conormal sheaf. -/
noncomputable def bidualityIso {Z X : Scheme.{u}} (i : Z ⟶ X) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf i)] :
    Scheme.Modules.dual (normalSheaf i) ≅ conormalSheaf i :=
  (biduality_isIso i).toIso.symm

/-- The inverse biduality identification is the canonical evaluation morphism. -/
theorem bidualityIso_inv {Z X : Scheme.{u}} (i : Z ⟶ X) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf i)] :
    (bidualityIso i r).inv = biduality i := rfl

end AlgebraicGeometry.Scheme.Hom
