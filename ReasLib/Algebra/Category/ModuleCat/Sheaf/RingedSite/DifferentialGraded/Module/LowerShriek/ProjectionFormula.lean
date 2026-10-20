/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.LowerShriek
public import ReasLib.CategoryTheory.Monoidal.Bimod.ChangeOfScalars.Tensor
public import ReasLib.CategoryTheory.Monoidal.Bimod.ProjectionFormula
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection formula for lower shriek of differential graded modules

For a monoidal adjunction on complexes, lower shriek of right DG modules satisfies the relative
tensor projection formula against left DG modules.  The target uses the actual restricted DGA and
the carrier-preserving restriction of the left module; the comparison with the monoidal image
presentation is handled by the generic change-of-coefficients tensor isomorphism.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule
open scoped SheafOfModules.RingedSite.LeftDifferentialGradedModule

noncomputable section

universe uC vC wC uD vD wD

namespace SheafOfModules.RingedSite.DifferentialGradedModule.LowerShriek.ProjectionFormula

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
variable [HasWeakSheafify JC AddCommGrpCat.{wC}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{wC}]
variable [HasWeakSheafify JD AddCommGrpCat.{wD}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{wD}]
variable [UnivLE.{max uC vC, wC}] [UnivLE.{max uD vD, wD}]
variable {OC : Sheaf JC CommRingCat.{wC}} {OD : Sheaf JD CommRingCat.{wD}}

variable {L : CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := JC) (𝒪 := OC)) ℤ ⥤
  CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := JD) (𝒪 := OD)) ℤ}
variable {R : CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := JD) (𝒪 := OD)) ℤ ⥤
  CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := JC) (𝒪 := OC)) ℤ}
variable (adj : L ⊣ R)
variable [R.LaxMonoidal] [L.OplaxMonoidal] [adj.IsMonoidal]
variable [adj.ProjectionFormulaMap]

-- Local declaration justification (search instability): pin the source and target sites of the
-- restricted coefficient algebra throughout the dependent bifunctor signatures below.
local notation "RAlg(" A ")" => LowerShriek.restrictedAlgebra
  (C := C) (D := D) (JC := JC) (JD := JD) (OC := OC) (OD := OD) (R := R) A

-- Local declaration justification (search instability): the left module is always over the target
-- site in this projection-formula API, while restricted left modules live over the source site.
local notation "LModD(" A ")" =>
  DifferentialGradedAlgebra.LeftModule (J := JD) (𝒪 := OD) A

-- Local declaration justification (search instability): reuse the endpoint-pinned coefficient
-- comparison without exposing all site parameters in the tensor normalization declaration.
local notation "RAlgIso(" A ")" => LowerShriek.coefficientIso
  (C := C) (D := D) (JC := JC) (JD := JD) (OC := OC) (OD := OD) (R := R) A

/-- Naturality of tensoring the lower shriek of a DG-module morphism with an ambient left
DG module. -/
theorem sourceMap_naturality (A : DGA(OD))
    {M M' : Mod(RAlg(A), d)} (f : M ⟶ M')
    {N N' : LModD(A)} (g : N ⟶ N') :
    (tensorFunctor ((functor adj A).obj M)).map g ≫
        (Bimod.whiskerRight (toBimodMap ((functor adj A).map f)) N').hom =
      (Bimod.whiskerRight (toBimodMap ((functor adj A).map f)) N).hom ≫
        (tensorFunctor ((functor adj A).obj M')).map g := sorry

/-- The source-side natural transformation induced by a morphism of localized right DG
modules. -/
noncomputable def sourceMap (A : DGA(OD))
    {M M' : Mod(RAlg(A), d)} (f : M ⟶ M') :
    tensorFunctor ((functor adj A).obj M) ⟶
      tensorFunctor ((functor adj A).obj M') where
  app N := (Bimod.whiskerRight (toBimodMap ((functor adj A).map f)) N).hom
  naturality := fun {X Y} g ↦
    sourceMap_naturality adj A f (N := X) (N' := Y) g

/-- The left side `jₗ M ⊗_A N` of the DG projection formula, functorial in both module
variables. -/
@[stacks 0FRX "lower shriek followed by differential graded relative tensor"]
noncomputable def sourceFunctor (A : DGA(OD)) :
    Mod(RAlg(A), d) ⥤ LModD(A) ⥤
      CochainComplex
        (DifferentialGradedAlgebra.moduleCategory (J := JD) (𝒪 := OD)) ℤ where
  obj M := tensorFunctor ((functor adj A).obj M)
  map f := sourceMap adj A f
  map_id := sorry
  map_comp := sorry

/-- Naturality of applying the ambient left adjoint to relative tensor after restricting a left
DG module. -/
theorem targetMap_naturality (A : DGA(OD))
    {M M' : Mod(RAlg(A), d)} (f : M ⟶ M')
    {N N' : LModD(A)} (g : N ⟶ N') :
    ((restrictionLeft (R := R) A ⋙
        tensorFunctor (J := JC) (𝒪 := OC) M ⋙ L).map g) ≫
        L.map (Bimod.whiskerRight
          (X := Mon.trivial _) (Y := (RAlg(A)).toMon) (Z := Mon.trivial _)
          (toBimodMap (J := JC) (𝒪 := OC) f)
          ((restrictionLeft (R := R) A).obj N')).hom =
      L.map (Bimod.whiskerRight
          (X := Mon.trivial _) (Y := (RAlg(A)).toMon) (Z := Mon.trivial _)
          (toBimodMap (J := JC) (𝒪 := OC) f)
          ((restrictionLeft (R := R) A).obj N)).hom ≫
        ((restrictionLeft (R := R) A ⋙
          tensorFunctor (J := JC) (𝒪 := OC) M' ⋙ L).map g) := sorry

/-- The target-side natural transformation induced by a morphism of localized right DG
modules. -/
noncomputable def targetMap (A : DGA(OD))
    {M M' : Mod(RAlg(A), d)} (f : M ⟶ M') :
    restrictionLeft (R := R) A ⋙
        tensorFunctor (J := JC) (𝒪 := OC) M ⋙ L ⟶
      restrictionLeft (R := R) A ⋙
        tensorFunctor (J := JC) (𝒪 := OC) M' ⋙ L where
  app N := L.map (Bimod.whiskerRight
    (X := Mon.trivial _) (Y := (RAlg(A)).toMon) (Z := Mon.trivial _)
    (toBimodMap (J := JC) (𝒪 := OC) f)
    ((restrictionLeft (R := R) A).obj N)).hom
  naturality := fun {X Y} g ↦
    targetMap_naturality (L := L) A f (N := X) (N' := Y) g

/-- The right side `jₗ(M ⊗_{A_U} N|_U)` of the DG projection formula, functorial in both
module variables. -/
@[stacks 0FRX "lower shriek of differential graded relative tensor after restriction"]
noncomputable def targetFunctor (A : DGA(OD)) :
    Mod(RAlg(A), d) ⥤ LModD(A) ⥤
      CochainComplex
        (DifferentialGradedAlgebra.moduleCategory (J := JD) (𝒪 := OD)) ℤ where
  obj M := restrictionLeft (R := R) A ⋙
    tensorFunctor (J := JC) (𝒪 := OC) M ⋙ L
  map f := targetMap (L := L) A f
  map_id := sorry
  map_comp := sorry

/-- The source tensor written in the right-module presentation used by the generic monoidal
projection formula. -/
@[stacks 0FRX "DG source tensor normalization"]
noncomputable def sourceIso (A : DGA(OD))
    (M : Mod(RAlg(A), d)) (N : LModD(A)) :
    tensor ((functor adj A).obj M) N ≅
      (((adj.rightModuleLowerShriek A.toMon).obj
        ((normalize (R := R) A).obj M)).tensorBimod N).X :=
  (Bimod.tensorRight N ⋙ Bimod.forget (Mon.trivial _)).mapIso
    (toBimodCounitIsoApp
      ((adj.rightModuleLowerShriek A.toMon).obj ((normalize (R := R) A).obj M)))

/-- The generic monoidal projection formula on the underlying complexes of the two balanced
tensors. -/
@[stacks 0FRX "underlying generic DG projection formula"]
noncomputable def monoidalIso (A : DGA(OD))
    (M : Mod(RAlg(A), d)) (N : LModD(A)) :
    (((adj.rightModuleLowerShriek A.toMon).obj
        ((normalize (R := R) A).obj M)).tensorBimod N).X ≅
      L.obj (((normalize (R := R) A).obj M).tensorBimod
        ((R.mapBimod A.toMon (Mon.trivial _)).obj N)).X :=
  (Bimod.forget (Mon.trivial _)).mapIso
    (CategoryTheory.Adjunction.RelativeTensor.iso adj A.toMon (Mon.trivial _)
      ((normalize (R := R) A).obj M) N)

/-- The localized balanced tensor in the monoidal-image presentation is canonically the tensor
over the actual restricted DGA with the actual restricted left DG module. -/
@[stacks 0FRX "restricted differential graded tensor normalization"]
noncomputable def restrictedTensorIso (A : DGA(OD))
    (M : Mod(RAlg(A), d)) (N : LModD(A)) :
    (((normalize (R := R) A).obj M).tensorBimod
        ((R.mapBimod A.toMon (Mon.trivial _)).obj N)).X ≅
      tensor (J := JC) (𝒪 := OC) M ((restrictionLeft (R := R) A).obj N) :=
  (Bimod.forget (Mon.trivial _)).mapIso
    (Bimod.ChangeOfScalars.tensorIso
      (R := Mon.trivial _) (A := (RAlg(A)).toMon)
      (B := R.mapMon.obj A.toMon) (T := R.mapMon.obj (Mon.trivial _))
      (RAlgIso(A)) (toBimod (J := JC) (𝒪 := OC) M)
      ((R.mapBimod A.toMon (Mon.trivial _)).obj N))

/-- Lemma 24.19.2 (0FRX), objectwise form: lower shriek commutes with relative tensor against
an ambient left DG module, using restriction to the actual localized DGA. -/
@[stacks 0FRX "differential graded lower-shriek projection formula"]
noncomputable def iso (A : DGA(OD))
    (M : Mod(RAlg(A), d)) (N : LModD(A)) :
    tensor ((functor adj A).obj M) N ≅
      L.obj (tensor (J := JC) (𝒪 := OC) M
        ((restrictionLeft (R := R) A).obj N)) :=
  sourceIso adj A M N ≪≫ monoidalIso adj A M N ≪≫
    L.mapIso (restrictedTensorIso (R := R) A M N)

/-- The objectwise DG projection formula is natural in the localized right module. -/
theorem iso_natural_left (A : DGA(OD))
    {M M' : Mod(RAlg(A), d)} (f : M ⟶ M')
    (N : LModD(A)) :
    ((sourceFunctor adj A).map f).app N ≫ (iso adj A M' N).hom =
      (iso adj A M N).hom ≫ ((targetFunctor (L := L) A).map f).app N := sorry

/-- The objectwise DG projection formula is natural in the ambient left module. -/
theorem iso_natural_right (A : DGA(OD))
    (M : Mod(RAlg(A), d))
    {N N' : LModD(A)} (g : N ⟶ N') :
    ((sourceFunctor adj A).obj M).map g ≫ (iso adj A M N').hom =
      (iso adj A M N).hom ≫ ((targetFunctor (L := L) A).obj M).map g := sorry

/-- The DG projection formula as a natural isomorphism in the ambient left module. -/
@[stacks 0FRX "DG projection formula natural in the left module"]
noncomputable def isoRight (A : DGA(OD))
    (M : Mod(RAlg(A), d)) :
    (sourceFunctor adj A).obj M ≅ (targetFunctor (L := L) A).obj M :=
  NatIso.ofComponents (iso adj A M) (iso_natural_right adj A M)

/-- The one-variable DG projection-formula isomorphisms are natural in the localized right
module. -/
theorem isoRight_naturality (A : DGA(OD))
    {M M' : Mod(RAlg(A), d)} (f : M ⟶ M') :
    (sourceFunctor adj A).map f ≫ (isoRight adj A M').hom =
      (isoRight adj A M).hom ≫ (targetFunctor (L := L) A).map f := sorry

/-- Lemma 24.19.2 (0FRX), reusable form: the DG lower-shriek projection formula as an
isomorphism of curried bifunctors, hence functorial in both module variables. -/
@[stacks 0FRX "DG projection formula natural in both module variables"]
noncomputable def natIso (A : DGA(OD)) :
    sourceFunctor adj A ≅ targetFunctor (L := L) A :=
  NatIso.ofComponents (isoRight adj A) (isoRight_naturality adj A)

/-- The component of the bifunctorial DG projection formula is the objectwise canonical
isomorphism. -/
@[simp]
theorem natIso_app_app (A : DGA(OD))
    (M : Mod(RAlg(A), d)) (N : LModD(A)) :
    ((natIso adj A).app M).app N = iso adj A M N := sorry

end SheafOfModules.RingedSite.DifferentialGradedModule.LowerShriek.ProjectionFormula

end
