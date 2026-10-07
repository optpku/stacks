module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Determinant.Construction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Determinant

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace ActualGlobalDeterminant

open ActualAffineRestriction

variable (X : Scheme.{u})

def underlyingIso {K L : Perfect X} (e : K ≅ L) : K.obj.obj ≅ L.obj.obj where
  hom := e.hom.hom.hom
  inv := e.inv.hom.hom
  hom_inv_id := by sorry
  inv_hom_id := by sorry

def affineObjectIso {K L : Perfect X} (e : K ≅ L) (U : X.affineOpens) :
    affineObject X K U ≅ affineObject X L U :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _ ((derived X U.1).mapIso (underlyingIso X e)))

def affineLineIso {K L : Perfect X} (e : K ≅ L) (U : X.affineOpens) :
    line X K U ≅ line X L U :=
  (ObjectProperty.ι _).mapIso
    ((CanonicalRingDeterminant.determinantFunctor Γ(X, U.1)).map ⟨affineObjectIso X e U⟩).iso

/-- Map compatible section families componentwise by the determinant of the
specified derived isomorphism. -/
def map {K L : Perfect X} (e : K ≅ L) : lineSheaf X K ⟶ lineSheaf X L where
  val :=
    { app := fun W ↦ ModuleCat.ofHom
        { toFun := fun s ↦ ⟨fun U ↦ (affineLineIso X e U.val).hom (s.val U), by sorry⟩
          map_add' := by sorry
          map_smul' := by sorry }
      naturality := by sorry }

def lineIso {K L : Perfect X} (e : K ≅ L) : lineSheaf X K ≅ lineSheaf X L where
  hom := map X e
  inv := map X e.symm
  hom_inv_id := by sorry
  inv_hom_id := by sorry

theorem lineSheaf_invertible (K : Perfect X) : Scheme.Modules.Invertible (lineSheaf X K) := by sorry

/-- The fixed, explicitly glued determinant functor on the core. -/
def determinantFunctor : Core (Perfect X) ⥤ Scheme.Modules.Invertible.Core X where
  obj K := ⟨⟨lineSheaf X K.of, lineSheaf_invertible X K.of⟩⟩
  map e := ⟨ObjectProperty.isoMk _ (lineIso X e.iso)⟩
  map_id := by sorry
  map_comp := by sorry

theorem rankZero_iso {K L : Perfect X} (e : K ≅ L) :
    isRankZero X K ↔ isRankZero X L := by sorry

theorem lineIso_delta {K L : Perfect X} (e : K ≅ L) (hK : isRankZero X K) :
    SheafOfModules.sectionsMap (lineIso X e).hom (delta X K hK) =
      delta X L ((rankZero_iso X e).mp hK) := by sorry

end ActualGlobalDeterminant
