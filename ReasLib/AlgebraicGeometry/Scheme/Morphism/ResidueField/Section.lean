/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.RingTheory.LocalRing.ResidueField.Surjective

/-!
# Residue fields and sections of scheme morphisms

This file records the residue-field consequences of a split scheme morphism.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A section induces a bijection on residue fields at the corresponding base point. -/
theorem section_residueFieldMap_bijective
    {X Y : Scheme.{u}} (e : Y ⟶ X) (f : X ⟶ Y) (hsec : e ≫ f = 𝟙 Y) (y : Y) :
    Function.Bijective (e.residueFieldMap y).hom := by
  let hy : f (e y) = y := by
    simpa using congrArg (fun k : Y ⟶ Y ↦ k y) hsec
  -- Re-express the section identity on stalks so that `e.stalkMap y` has an explicit right
  -- inverse after transporting along the point equality `f (e y) = y`.
  have hstalk_comp :
      f.stalkMap (e y) ≫ e.stalkMap y =
        (Y.presheaf.stalkCongr (.of_eq hy)).hom := by
    have htmp :=
      (Scheme.Hom.stalkMap_congr_hom (f := e ≫ f) (g := (𝟙 Y : Y ⟶ Y)) hsec (x := y))
    rw [Scheme.Hom.stalkMap_comp] at htmp
    simpa using htmp
  let retraction : Y.presheaf.stalk y ⟶ X.presheaf.stalk (e y) :=
    (Y.presheaf.stalkCongr (.of_eq hy.symm)).hom ≫ f.stalkMap (e y)
  have hretraction : retraction ≫ e.stalkMap y = 𝟙 _ := by
    -- The transport isomorphism cancels the stalk-level section identity.
    simp [retraction, hstalk_comp, Category.assoc]
  have hsurj : Function.Surjective (e.stalkMap y).hom := by
    intro t
    refine ⟨retraction.hom t, ?_⟩
    change (retraction ≫ e.stalkMap y).hom t = t
    simpa [hretraction]
  -- A surjective local ring map induces a bijection on residue fields.
  change Function.Bijective (IsLocalRing.ResidueField.map (e.stalkMap y).hom)
  exact RingHom.ResidueField.map_bijective_of_surjective (e.stalkMap y).hom hsurj

/-- A morphism split by a section induces a bijection on residue fields at the image of the
section point. -/
theorem residueFieldMap_bijective_of_section
    {X Y : Scheme.{u}} (e : Y ⟶ X) (f : X ⟶ Y) (hsec : e ≫ f = 𝟙 Y) (y : Y) :
    Function.Bijective (f.residueFieldMap (e y)).hom := by
  let hy : f (e y) = y := by
    simpa using congrArg (fun k : Y ⟶ Y ↦ k y) hsec
  have he_bij : Function.Bijective (e.residueFieldMap y).hom :=
    section_residueFieldMap_bijective e f hsec y
  -- The residue-field map of `f` becomes inverse to that of the section after transporting
  -- the source residue field along `hy : f (e y) = y`.
  have hcomp :
      f.residueFieldMap (e y) ≫ e.residueFieldMap y =
        (Y.residueFieldCongr hy).hom := by
    have htmp :=
      (Scheme.Hom.residueFieldMap_congr
        (f := e ≫ f) (g := (𝟙 Y : Y ⟶ Y)) hsec (x := y))
    rw [Scheme.residueFieldMap_comp] at htmp
    simpa using htmp
  constructor
  · exact RingHom.injective _
  · intro x
    let y' : Y.residueField (f (e y)) :=
      (Y.residueFieldCongr hy.symm).hom ((e.residueFieldMap y).hom x)
    refine ⟨y', ?_⟩
    apply he_bij.injective
    -- Applying the section residue-field map reduces the claim to the transport identity `hcomp`.
    change (f.residueFieldMap (e y) ≫ e.residueFieldMap y).hom y' =
      (e.residueFieldMap y).hom x
    rw [hcomp]
    change (((Y.residueFieldCongr hy.symm).hom ≫ (Y.residueFieldCongr hy).hom).hom
        ((e.residueFieldMap y).hom x)) = (e.residueFieldMap y).hom x
    simp

end AlgebraicGeometry.Scheme.Hom
