/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.BaseChange
public import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# The scheme glued from finite locally constant affine algebras

The actual affine spectra and restriction maps form native relative gluing data over the
directed affine-open cover. Their cartesian squares come from the explicit algebra
base-change inverse. The resulting scheme and structure morphism are concrete gluing data.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.FiniteLocallyConstant

variable {X : Scheme.{u}}
variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]
variable (F : Sheaf X.smallEtaleTopology (Type (u + 1))) [Sheaf.IsFiniteLocallyConstant F]

/-- A base affine open regarded as its actual object of the small étale site. -/
abbrev affineOpenEtale (U : X.affineOpens) : X.Etale :=
  Scheme.Etale.mk (U : X.Opens).ι

instance affineOpenEtale_isAffine (U : X.affineOpens) : IsAffine (affineOpenEtale U).left :=
  U.property

/-- Inclusion of base affine opens is the corresponding actual map of étale objects. -/
def affineOpenEtaleMap {U V : X.affineOpens} (h : U ≤ V) : affineOpenEtale U ⟶ affineOpenEtale V :=
  MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι h)

/-- The concrete descended affine spectra glue along the implemented restriction maps. -/
def representationGluingData : X.directedAffineCover.RelativeGluingData where
  functor :=
    { obj := fun U : X.affineOpens ↦ affineRepresentation F (affineOpenEtale U)
      map := fun {U V : X.affineOpens} h ↦ affineRestrictionMap F (affineOpenEtaleMap (leOfHom h))
      map_id := sorry
      map_comp := sorry }
  natTrans :=
    { app := fun U : X.affineOpens ↦ affineRepresentationMap F (affineOpenEtale U)
      naturality := sorry }
  equifibered := fun {U V : X.affineOpens} h ↦
    affineRestriction_isPullback F (affineOpenEtaleMap (leOfHom h))

/-- The actual global scheme obtained by native relative gluing of the affine descended spectra. -/
abbrev representation : Scheme.{u} := (representationGluingData F).glued

/-- The global structure morphism is the native glued morphism to the base. -/
def representationMap : representation F ⟶ X := (representationGluingData F).toBase

/-- Each affine representing scheme is an actual open chart of the global scheme. -/
def representationChart (U : X.affineOpens) :
    affineRepresentation F (affineOpenEtale U) ⟶ representation F :=
  colimit.ι (representationGluingData F).functor U

/-- The inverse-image affine chart isomorphism comes from native open gluing in both directions. -/
def representationLocalIso (U : X.affineOpens) :
    ((representationMap F) ⁻¹ᵁ (U : X.Opens)).toScheme ≅
      affineRepresentation F (affineOpenEtale U) :=
  (representation F).isoOfEq
      (by
        have h := (representationGluingData F).toBase_preimage_eq_opensRange_ι U
        change (representationMap F) ⁻¹ᵁ (U : X.Opens).ι.opensRange = _ at h
        rw [Scheme.Opens.opensRange_ι] at h
        exact h) ≪≫
    (colimit.ι (representationGluingData F).functor U).isoOpensRange.symm

/-- The actual local inverse-image isomorphisms supply affineness of the global structure map. -/
instance representationMap_isAffineHom : IsAffineHom (representationMap F) where
  isAffine_preimage U hU :=
    letI : IsAffine (affineOpenEtale (X := X) ⟨U, hU⟩).left := hU
    letI : IsAffine (affineRepresentation F (affineOpenEtale ⟨U, hU⟩)) :=
      inferInstanceAs (IsAffine (Spec (CommRingCat.of (affineAlgebra (F := F) (affineOpenEtale ⟨U, hU⟩)))))
    letI := (representationLocalIso F ⟨U, hU⟩).isIso_hom
    IsAffine.of_isIso (representationLocalIso F ⟨U, hU⟩).hom

/-- The actual global morphism is finite, as are its descended affine charts. -/
instance representationMap_isFinite : IsFinite (representationMap F) := sorry

/-- The actual global morphism is étale, as are its descended affine charts. -/
instance representationMap_etale : Etale (representationMap F) := sorry

/-- The finite étale object constructed from the supplied locally constant sheaf. -/
def finiteEtaleRepresentation : FiniteEtale X :=
  MorphismProperty.Over.mk ⊤ (representationMap F) ⟨inferInstance, inferInstance⟩

/-- The constructed global scheme as an object of the original small étale site. -/
def representationEtale : X.Etale := Scheme.Etale.mk (representationMap F)

end AlgebraicGeometry.Scheme.FiniteLocallyConstant
