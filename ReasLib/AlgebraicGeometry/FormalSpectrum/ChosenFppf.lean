/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.ULift
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Full
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Affine
public import ReasLib.AlgebraicGeometry.FormalSpectrum.PresheafColimit

/-!
# Formal spectra on the full chosen fppf site

The weak-ideal quotient diagram defines a sheaf colimit with canonical quotient-stage maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology IsLocalRing
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace.FppfFormalSpectrum

/-- The universe-lifted reverse-inclusion order on weak ideals is directed. -/
instance instIsDirected (A : Type u) [CommRing A] [TopologicalSpace A] :
    IsDirected (ULift.{u + 1} (WeakIdealOfDefinition A)) (· ≤ ·) :=
  sorry

/-- The lifted diagram of affine quotient spectra in the full chosen fppf slice. -/
def affineThickenings (A : Type u) [CommRing A] [TopologicalSpace A]
    {base : Scheme.{u}} (structureHom : Spec (.of A) ⟶ base) :
    ULift.{u + 1} (WeakIdealOfDefinition A) ⥤ full.bigAffineSite base :=
  (full.bigAffineObjects base).lift
    (({ toFun := ULift.down, monotone' := fun _ _ comparison ↦ comparison } :
      ULift.{u + 1} (WeakIdealOfDefinition A) →o WeakIdealOfDefinition A).toFunctor ⋙
        thickenings A structureHom)
    (fun ideal ↦ thickenings_obj_isAffine A structureHom ideal.down)

/-- The scheme underlying a lifted affine stage is its weak-ideal quotient spectrum. -/
theorem affineThickenings_obj (A : Type u) [CommRing A] [TopologicalSpace A]
    {base : Scheme.{u}} (structureHom : Spec (.of A) ⟶ base)
    (ideal : ULift.{u + 1} (WeakIdealOfDefinition A)) :
    (full.bigAffineToScheme base).obj ((affineThickenings A structureHom).obj ideal) =
      Spec (.of (A ⧸ ideal.down.ideal)) :=
  rfl

/-- The formal spectrum is the sheaf colimit of its lifted weak-ideal quotient diagram. -/
def spf (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    {base : Scheme.{u}} (structureHom : Spec (.of A) ⟶ base)
    [HasWeakSheafify (full.bigTopology base) (Type (u + 1))] :
    Sheaf (full.bigTopology base) (Type (u + 1)) :=
  colimit (affineThickenings A structureHom ⋙ full.bigAffineInclusion base ⋙
    (full.bigTopology base).sheafifiedRepresentableFunctor)

/-- The formal spectrum recovers its defining sheaf colimit. -/
theorem spf_eq (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    {base : Scheme.{u}} (structureHom : Spec (.of A) ⟶ base)
    [HasWeakSheafify (full.bigTopology base) (Type (u + 1))] :
    spf A structureHom =
      colimit (affineThickenings A structureHom ⋙ full.bigAffineInclusion base ⋙
        (full.bigTopology base).sheafifiedRepresentableFunctor) :=
  rfl

/-- Each sheafified quotient stage maps to the formal spectrum by its colimit leg. -/
def spfι (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    {base : Scheme.{u}} (structureHom : Spec (.of A) ⟶ base)
    [HasWeakSheafify (full.bigTopology base) (Type (u + 1))]
    (ideal : ULift.{u + 1} (WeakIdealOfDefinition A)) :
    (full.bigTopology base).sheafifiedRepresentable
      ((full.bigAffineInclusion base).obj ((affineThickenings A structureHom).obj ideal)) ⟶
        spf A structureHom :=
  colimit.ι (affineThickenings A structureHom ⋙ full.bigAffineInclusion base ⋙
    (full.bigTopology base).sheafifiedRepresentableFunctor) ideal

/-- The residue-field morphism is the colimit leg at the maximal weak ideal. -/
def specResidue (A : Type u) [CommRing A] [IsLocalRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    {base : Scheme.{u}} (structureHom : Spec (.of A) ⟶ base)
    [HasWeakSheafify (full.bigTopology base) (Type (u + 1))]
    (weakMaximal : TopologicalRing.Ideal.IsWeakIdealOfDefinition (maximalIdeal A)) :
    (full.bigTopology base).sheafifiedRepresentable
      (stage A structureHom (WeakIdealOfDefinition.maximal weakMaximal)) ⟶
        spf A structureHom :=
  spfι A structureHom (ULift.up (WeakIdealOfDefinition.maximal weakMaximal))

/-- The residue-field morphism recovers exactly its maximal-ideal colimit leg. -/
theorem specResidue_eq (A : Type u) [CommRing A] [IsLocalRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    {base : Scheme.{u}} (structureHom : Spec (.of A) ⟶ base)
    [HasWeakSheafify (full.bigTopology base) (Type (u + 1))]
    (weakMaximal : TopologicalRing.Ideal.IsWeakIdealOfDefinition (maximalIdeal A)) :
    specResidue A structureHom weakMaximal =
      spfι A structureHom (ULift.up (WeakIdealOfDefinition.maximal weakMaximal)) :=
  rfl

/-- A sheaf morphism is a thickening when it is relatively representable with scheme-thickening pullbacks. -/
def thickening (base : Scheme.{u})
    [HasWeakSheafify (full.bigTopology base) (Type (u + 1))] :
    MorphismProperty (Sheaf (full.bigTopology base) (Type (u + 1))) :=
  MorphismProperty.relative
    (full.bigTopology base).sheafifiedRepresentableFunctor
    (MorphismProperty.inverseImage
      (fun _ _ arrow ↦ IsThickening arrow : MorphismProperty Scheme.{u})
      (full.bigToScheme base))

/-- The thickening property records relative representability and thickening of every represented pullback. -/
theorem thickening_iff (base : Scheme.{u})
    [HasWeakSheafify (full.bigTopology base) (Type (u + 1))]
    {source target : Sheaf (full.bigTopology base) (Type (u + 1))}
    (arrow : source ⟶ target) :
    thickening base arrow ↔
      (full.bigTopology base).sheafifiedRepresentableFunctor.relativelyRepresentable arrow ∧
        ∀ ⦃test pullbackTest : full.bigSite base⦄
          (testMap : (full.bigTopology base).sheafifiedRepresentable test ⟶ target)
          (first : (full.bigTopology base).sheafifiedRepresentable pullbackTest ⟶ source)
          (second : pullbackTest ⟶ test),
          IsPullback first ((full.bigTopology base).sheafifiedRepresentableFunctor.map second)
            arrow testMap → IsThickening ((full.bigToScheme base).map second) :=
  Iff.rfl

/-- The formal spectrum satisfies the fixed-site representable presentation condition. -/
instance instIsCoequalizerOfRepresentables_spf (A : Type u) [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    {base : Scheme.{u}} (structureHom : Spec (.of A) ⟶ base)
    [HasWeakSheafify (full.bigTopology base) (Type (u + 1))]
    [HasPullbacks (Sheaf (full.bigTopology base) (Type (u + 1)))] :
    IsCoequalizerOfRepresentables (spf A structureHom) :=
  sorry

/-- The sheaf formal spectrum of a weakly admissible ring is an affine formal algebraic space. -/
instance instIsAffineFormalAlgebraicSpace_spf (A : Type u) [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    {base : Scheme.{u}} (structureHom : Spec (.of A) ⟶ base)
    [HasWeakSheafify (full.bigTopology base) (Type (u + 1))]
    [HasPullbacks (Sheaf (full.bigTopology base) (Type (u + 1)))] :
    IsAffineFormalAlgebraicSpace (spf A structureHom) :=
  sorry

/-- The maximal weak ideal defines a thickening from the residue-field spectrum into the formal spectrum. -/
theorem specResidue_isThickening (A : Type u) [CommRing A] [IsLocalRing A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    {base : Scheme.{u}} (structureHom : Spec (.of A) ⟶ base)
    [HasWeakSheafify (full.bigTopology base) (Type (u + 1))]
    (weakMaximal : TopologicalRing.Ideal.IsWeakIdealOfDefinition (maximalIdeal A)) :
    thickening base (specResidue A structureHom weakMaximal) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace.FppfFormalSpectrum
