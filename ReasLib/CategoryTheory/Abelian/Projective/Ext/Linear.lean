/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import ReasLib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Comparison

@[expose] public section

/-!
# Linear projective-resolution computations of Ext

This file equips Hom-complex cohomology classes with their canonical transported module
structure and upgrades the projective-resolution computation of `Ext` from an additive
equivalence to a linear equivalence.
@stack 0EH2
-/

open CategoryTheory CategoryTheory.Abelian ComplexShape HomotopyCategory

noncomputable section

universe w v u

namespace CochainComplex.HomComplex.CohomologyClass

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The canonical scalar action on Hom-complex cohomology classes, transported from shifted
morphisms in the homotopy category. -/
@[stacks 0EH2 "scalar action on Hom-complex cohomology classes"]
noncomputable instance module (R : Type w) [Ring R] [Linear R C]
    (K L : CochainComplex C ℤ) (n : ℤ) : Module R (CohomologyClass K L n) :=
  (homAddEquiv (K := K) (L := L) (n := n)).module R

/-- Hom-complex cohomology classes, bundled with the module structure transported from
shifted morphisms in the homotopy category. -/
@[stacks 0EH2 "module of Hom-complex cohomology classes"]
noncomputable def moduleCat (R : Type w) [Ring R] [Linear R C]
    (K L : CochainComplex C ℤ) (n : ℤ) : ModuleCat.{v} R :=
  ModuleCat.of R (CohomologyClass K L n)

/-- Hom-complex cohomology classes identify linearly with shifted morphisms in the homotopy
category. -/
@[stacks 0EH2 "linear Hom-complex cohomology comparison"]
noncomputable def homLinearEquiv (R : Type w) [Ring R] [Linear R C]
    (K L : CochainComplex C ℤ) (n : ℤ) :
    (moduleCat R K L n : Type v) ≃ₗ[R]
      ((HomotopyCategory.quotient C (up ℤ)).obj K ⟶
        (HomotopyCategory.quotient C (up ℤ)).obj (L⟦n⟧)) :=
  (homAddEquiv (K := K) (L := L) (n := n)).linearEquiv R

end CochainComplex.HomComplex.CohomologyClass

namespace CategoryTheory.ProjectiveResolution

variable {R : Type u} [CommRing R] [Small.{v} R]
  {X Y : ModuleCat.{v} R} (P : ProjectiveResolution X) {n : ℕ}

/-- The degree-`n` three-term window in the enriched Hom complex associated to a projective
resolution and a target module. -/
@[stacks 0EH2 "degree window in a projective-resolution Hom complex"]
abbrev extHomWindow (Y : ModuleCat.{v} R) (n : ℕ) :
    ShortComplex (ModuleCat.{v} R) :=
  (CochainComplex.HomComplex.moduleComplex R P.cochainComplex
    ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj Y)).sc (n : ℤ)

/-- Mathlib's additive projective-resolution computation of `Ext` respects the canonical scalar
action transported to Hom-complex cohomology classes. -/
@[stacks 0EH2 "linearity of the projective-resolution Ext comparison"]
theorem extAddEquivCohomologyClass_map_smul (r : R) (x : Ext X Y n) :
    P.extAddEquivCohomologyClass (r • x) =
      (r • P.extAddEquivCohomologyClass x :
        (CochainComplex.HomComplex.CohomologyClass.moduleCat R
          P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj Y)
          (n : ℤ) : Type v)) := sorry

/-- The linear equivalence computing `Ext` from any projective resolution in `ModuleCat`. -/
@[stacks 0EH2 "linear Ext computation from a projective resolution"]
noncomputable def extLinearEquivCohomologyClass :
    Ext X Y n ≃ₗ[R]
      (CochainComplex.HomComplex.CohomologyClass.moduleCat R
        P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj Y)
        (n : ℤ) : Type v) :=
  { __ := P.extAddEquivCohomologyClass
    map_smul' := extAddEquivCohomologyClass_map_smul P }

/-- The linear equivalence computing `Ext` as the homology of the enriched module-valued Hom
complex associated to any projective resolution in `ModuleCat`. -/
@[stacks 0EH2 "linear Ext computation as enriched Hom-complex homology"]
noncomputable def extLinearEquivHomology :
    Ext X Y n ≃ₗ[R]
      (CochainComplex.HomComplex.moduleComplex R P.cochainComplex
        ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj Y)).homology (n : ℤ) :=
  P.extLinearEquivCohomologyClass |>.trans
    ((CochainComplex.HomComplex.CohomologyClass.homLinearEquiv R
      P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj Y)
      (n : ℤ)).trans
        (CochainComplex.HomComplex.Module.homologyHomLinearEquiv R
          P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj Y)
          (n : ℤ)).symm)

/-- The canonical linear computation of `Ext` as homology of the degree-`n` three-term window in
the enriched Hom complex. -/
@[stacks 0EH2 "linear Ext computation from a Hom-complex degree window"]
noncomputable def extLinearEquivWindowHomology :
    Ext X Y n ≃ₗ[R] (P.extHomWindow Y n).homology :=
  P.extLinearEquivHomology

/-- The underlying function of the linear projective-resolution equivalence is mathlib's
canonical additive projective-resolution equivalence. -/
@[simp, stacks 0EH2 "linear projective-resolution Ext comparison on classes"]
theorem extLinearEquivCohomologyClass_apply (x : Ext X Y n) :
    P.extLinearEquivCohomologyClass x = P.extAddEquivCohomologyClass x := sorry

/-- The inverse of the linear projective-resolution equivalence is mathlib's canonical
inverse additive equivalence. -/
@[simp, stacks 0EH2 "inverse linear projective-resolution Ext comparison on classes"]
theorem extLinearEquivCohomologyClass_symm_apply
    (x : CochainComplex.HomComplex.CohomologyClass
      P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj Y) (n : ℤ)) :
    P.extLinearEquivCohomologyClass.symm x =
      P.extAddEquivCohomologyClass.symm x := sorry

/-- Evaluation of the enriched Hom-complex homology computation through the canonical
cohomology-class and shifted-Hom identifications. -/
@[simp, stacks 0EH2 "linear Ext-to-Hom-complex homology formula"]
theorem extLinearEquivHomology_apply (x : Ext X Y n) :
    P.extLinearEquivHomology x =
      (CochainComplex.HomComplex.Module.homologyHomLinearEquiv R
        P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj Y)
        (n : ℤ)).symm
          (CochainComplex.HomComplex.CohomologyClass.homLinearEquiv R
            P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj Y)
            (n : ℤ) (P.extAddEquivCohomologyClass x)) := sorry

/-- Evaluation of the inverse enriched Hom-complex homology computation through the canonical
shifted-Hom and cohomology-class identifications. -/
@[simp, stacks 0EH2 "inverse Hom-complex homology-to-Ext formula"]
theorem extLinearEquivHomology_symm_apply
    (x : (CochainComplex.HomComplex.moduleComplex R P.cochainComplex
      ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj Y)).homology (n : ℤ)) :
    P.extLinearEquivHomology.symm x =
      P.extAddEquivCohomologyClass.symm
        ((CochainComplex.HomComplex.CohomologyClass.homLinearEquiv R
          P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj Y)
          (n : ℤ)).symm
            (CochainComplex.HomComplex.Module.homologyHomLinearEquiv R
              P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj Y)
              (n : ℤ) x)) := sorry

end CategoryTheory.ProjectiveResolution
