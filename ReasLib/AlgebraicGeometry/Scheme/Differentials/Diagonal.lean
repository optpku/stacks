/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Affine

/-!
# Relative differentials and the diagonal

For a morphism of schemes, the difference of the two projection sections of its diagonal
defines the canonical comparison from relative differentials to the conormal sheaf of the
diagonal.
-/

@[expose] public section

open CategoryTheory Limits TopCat TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials.Diagonal

variable {X S : Scheme.{u}}

/-- The inverse-image structure-sheaf map of the diagonal of a scheme morphism. -/
noncomputable abbrev diagonalStructureMap (f : X ⟶ S) :
    (TopCat.Sheaf.pullback CommRingCat.{u} (pullback.diagonal f).base).obj
        (pullback f f).sheaf ⟶ X.sheaf :=
  RingedSpace.Hom.inverseImageStructureSheafHomComm (pullback.diagonal f).toShHom

/-- The first projection gives a section of the structure-sheaf map of the diagonal. -/
noncomputable def fstSection (f : X ⟶ S) :
    X.sheaf ⟶
      (TopCat.Sheaf.pullback CommRingCat.{u} (pullback.diagonal f).base).obj
        (pullback f f).sheaf :=
  (Adjunction.leftAdjointIdIso
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (𝟙 (X : TopCat)))
    (Iso.refl _)).inv.app X.sheaf ≫
    (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
      (congrArg (fun g : X ⟶ X ↦ g.base) (pullback.diagonal_fst f))).inv.app X.sheaf ≫
    (RingedSpace.Hom.StructureSheaf.compIso
      (pullback.diagonal f).toShHom (pullback.fst f f).toShHom).inv ≫
    RingedSpace.Hom.StructureSheaf.pullbackMap
      (pullback.diagonal f).toShHom (pullback.fst f f).toShHom

/-- The second projection gives a section of the structure-sheaf map of the diagonal. -/
noncomputable def sndSection (f : X ⟶ S) :
    X.sheaf ⟶
      (TopCat.Sheaf.pullback CommRingCat.{u} (pullback.diagonal f).base).obj
        (pullback f f).sheaf :=
  (Adjunction.leftAdjointIdIso
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (𝟙 (X : TopCat)))
    (Iso.refl _)).inv.app X.sheaf ≫
    (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
      (congrArg (fun g : X ⟶ X ↦ g.base) (pullback.diagonal_snd f))).inv.app X.sheaf ≫
    (RingedSpace.Hom.StructureSheaf.compIso
      (pullback.diagonal f).toShHom (pullback.snd f f).toShHom).inv ≫
    RingedSpace.Hom.StructureSheaf.pullbackMap
      (pullback.diagonal f).toShHom (pullback.snd f f).toShHom

/-- The first projection section splits the structure-sheaf map of the diagonal. -/
theorem fstSection_comp_diagonalStructureMap (f : X ⟶ S) :
    fstSection f ≫ diagonalStructureMap f = 𝟙 X.sheaf := sorry

/-- The second projection section splits the structure-sheaf map of the diagonal. -/
theorem sndSection_comp_diagonalStructureMap (f : X ⟶ S) :
    sndSection f ≫ diagonalStructureMap f = 𝟙 X.sheaf := sorry

/-- Pulling a section from the base through either projection gives the same section along the
diagonal. -/
theorem base_comp_fstSection_eq_base_comp_sndSection (f : X ⟶ S) :
    RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom ≫ fstSection f =
      RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom ≫ sndSection f := sorry

/-- A local section maps to the conormal cotangent class of the difference between its second
and first projection sections. -/
noncomputable def comparisonSection (f : X ⟶ S) {U : (Opens X)ᵒᵖ}
    (a : X.presheaf.obj U) :
    (Scheme.Hom.conormalSheaf
      (pullback.diagonal f : X ⟶ pullback f f)).val.obj U :=
  (conormalSourcePresheafUnit (diagonalStructureMap f)).app U
    ((conormalIdeal (diagonalStructureMap f) U).toCotangent
      ⟨(sndSection f).hom.app U a - (fstSection f).hom.app U a, by
        change (diagonalStructureMap f).hom.app U
          ((sndSection f).hom.app U a - (fstSection f).hom.app U a) = 0
        rw [map_sub]
        have hfst : (diagonalStructureMap f).hom.app U
            ((fstSection f).hom.app U a) = a := by
          have h := congrArg (fun g ↦ g.hom.app U a)
            (fstSection_comp_diagonalStructureMap f)
          change (diagonalStructureMap f).hom.app U
            ((fstSection f).hom.app U a) = a at h
          exact h
        have hsnd : (diagonalStructureMap f).hom.app U
            ((sndSection f).hom.app U a) = a := by
          have h := congrArg (fun g ↦ g.hom.app U a)
            (sndSection_comp_diagonalStructureMap f)
          change (diagonalStructureMap f).hom.app U
            ((sndSection f).hom.app U a) = a at h
          exact h
        rw [hsnd, hfst, sub_self]⟩)

/-- The section map defining the diagonal comparison is additive. -/
theorem comparisonSection_add (f : X ⟶ S) {U : (Opens X)ᵒᵖ}
    (a b : X.presheaf.obj U) :
    comparisonSection f (a + b) = comparisonSection f a + comparisonSection f b := sorry

/-- The section map defining the diagonal comparison satisfies the Leibniz rule. -/
theorem comparisonSection_mul (f : X ⟶ S) {U : (Opens X)ᵒᵖ}
    (a b : X.presheaf.obj U) :
    comparisonSection f (a * b) =
      a • comparisonSection f b + b • comparisonSection f a := sorry

/-- The section map defining the diagonal comparison commutes with restriction. -/
theorem comparisonSection_naturality (f : X ⟶ S)
    {U V : (Opens X)ᵒᵖ} (rho : U ⟶ V) (a : X.presheaf.obj U) :
    comparisonSection f (X.presheaf.map rho a) =
      (Scheme.Hom.conormalSheaf
        (pullback.diagonal f : X ⟶ pullback f f)).val.map rho
        (comparisonSection f a) := sorry

/-- The section map defining the diagonal comparison vanishes on sections pulled back from the
base. -/
theorem comparisonSection_base (f : X ⟶ S) {U : (Opens X)ᵒᵖ}
    (a : ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).obj.obj U) :
    comparisonSection f
      ((RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom).hom.app U a) = 0 := sorry

/-- The difference of the two projection sections as an `S`-relative derivation with values in
the conormal sheaf of the diagonal. -/
noncomputable def comparisonDerivation (f : X ⟶ S) :
    RingedSpace.Hom.derivations f.toShHom
      (Scheme.Hom.conormalSheaf (pullback.diagonal f : X ⟶ pullback f f)) where
  d {_} := AddMonoidHom.mk' (comparisonSection f) (comparisonSection_add f)
  d_mul := comparisonSection_mul f
  d_map := comparisonSection_naturality f
  d_app := comparisonSection_base f

/-- The canonical comparison from relative differentials to the conormal sheaf of the
diagonal. -/
noncomputable def comparison (f : X ⟶ S) :
    Ω[f.toShHom] ⟶
      Scheme.Hom.conormalSheaf (pullback.diagonal f : X ⟶ pullback f f) :=
  RingedSpace.Hom.differentialDesc f.toShHom (comparisonDerivation f)

/-- A morphism from relative differentials is the diagonal comparison when it carries every
universal differential to the corresponding difference-of-projections conormal class. -/
def IsComparison (f : X ⟶ S)
    (tau : Ω[f.toShHom] ⟶
      Scheme.Hom.conormalSheaf (pullback.diagonal f : X ⟶ pullback f f)) : Prop :=
  ∀ {U : (Opens X)ᵒᵖ} (a : X.presheaf.obj U),
    tau.val.app U ((d[f.toShHom]).d a) = comparisonSection f a

/-- The canonical diagonal comparison satisfies its universal-differential characterization. -/
theorem comparison_isComparison (f : X ⟶ S) :
    IsComparison f (comparison f) := sorry

/-- A morphism satisfying the universal-differential characterization is the canonical diagonal
comparison. -/
theorem eq_comparison (f : X ⟶ S)
    {tau : Ω[f.toShHom] ⟶
      Scheme.Hom.conormalSheaf (pullback.diagonal f : X ⟶ pullback f f)}
    (h_tau : IsComparison f tau) :
    tau = comparison f := sorry

/-- The canonical comparison from relative differentials to the conormal sheaf of the diagonal
is an isomorphism. -/
noncomputable instance comparison_isIso (f : X ⟶ S) :
    IsIso (comparison f) := sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials.Diagonal
