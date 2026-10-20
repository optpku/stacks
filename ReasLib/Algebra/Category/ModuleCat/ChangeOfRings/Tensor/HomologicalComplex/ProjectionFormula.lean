/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor.HomologicalComplex
import Mathlib.Tactic.CrossRefAttribute

/-!
# Change-of-rings projection formula for cochain complexes

@stack 064M

For a ring map `f : R →+* S`, restriction of scalars identifies
`L ⊗[S] (S ⊗[R] K)` with `L|_R ⊗[R] K`.  This file keeps the construction at four reusable
layers: modules, arbitrary homological complexes, cochain bicomplexes, and unbounded totalized
tensor products.

The comparison maps are explicit tensor-product cancellation maps and coproduct comparisons.
In particular, the final isomorphism does not choose an inverse from a separately asserted
`IsIso` proposition.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape
open scoped TensorProduct

universe u v

namespace ModuleCat.RestrictScalars

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The module-level projection formula for a fixed `S`-module.  The local scalar-action pins
identify the action induced by `f` with the action expected by the canonical tensor-cancellation
map; exporting either pin would create a competing global module structure. -/
@[stacks 064M "module change-of-rings projection formula"]
noncomputable def tensorExtendComponentIso
    (f : R →+* S) (M : ModuleCat.{u} S) (X : ModuleCat.{u} R) :
    ((ModuleCat.extendScalars f) ⋙ (curriedTensor (ModuleCat S)).obj M ⋙
      (ModuleCat.restrictScalars.{u} f)).obj X ≅
      ((curriedTensor (ModuleCat R)).obj
        ((ModuleCat.restrictScalars f).obj M)).obj X :=
  letI : Algebra R S := f.toAlgebra
  letI : Module R M := Module.compHom M f
  letI : IsScalarTower R S M :=
    IsScalarTower.restrictScalars R S M
  (ModuleCat.restrictScalars f).mapIso
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M X).toModuleIso)

/-- Naturality of `tensorExtendComponentIso` in the `R`-module. -/
@[reassoc, stacks 064M "naturality of the module projection formula"]
theorem tensorExtendComponentIso_hom_naturality
    (f : R →+* S) (M : ModuleCat.{u} S)
    {X Y : ModuleCat.{u} R} (g : X ⟶ Y) :
    (((ModuleCat.extendScalars f) ⋙ (curriedTensor (ModuleCat S)).obj M ⋙
        (ModuleCat.restrictScalars.{u} f)).map g) ≫
        (tensorExtendComponentIso f M Y).hom =
      (tensorExtendComponentIso f M X).hom ≫
        ((curriedTensor (ModuleCat R)).obj
          ((ModuleCat.restrictScalars f).obj M)).map g := sorry

/-- For a fixed `S`-module `M`, restriction after tensoring `M` with an extended module is
naturally isomorphic to tensoring the restricted `M` over `R`. -/
@[stacks 064M "natural module change-of-rings projection formula"]
noncomputable def tensorExtendNatIso (f : R →+* S) (M : ModuleCat.{u} S) :
    (ModuleCat.extendScalars f) ⋙ (curriedTensor (ModuleCat S)).obj M ⋙
        (ModuleCat.restrictScalars.{u} f) ≅
      (curriedTensor (ModuleCat R)).obj
        ((ModuleCat.restrictScalars f).obj M) :=
  NatIso.ofComponents (tensorExtendComponentIso f M)
    (tensorExtendComponentIso_hom_naturality f M)

/-- The module projection formula lifted degreewise to homological complexes of shape `c`. -/
@[stacks 064M "natural complex change-of-rings projection formula"]
noncomputable def tensorExtendComplexNatIso
    (f : R →+* S) (M : ModuleCat.{u} S) (c : ComplexShape ι) :
    ((ModuleCat.extendScalars f) ⋙ (curriedTensor (ModuleCat S)).obj M ⋙
        (ModuleCat.restrictScalars.{u} f)).mapHomologicalComplex c ≅
      ((curriedTensor (ModuleCat R)).obj
        ((ModuleCat.restrictScalars f).obj M)).mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex (tensorExtendNatIso f M) c

/-- The objectwise complex projection formula induced by `tensorExtendComplexNatIso`. -/
@[stacks 064M "complex change-of-rings projection formula"]
noncomputable def tensorExtendComplexIso
    (f : R →+* S) (M : ModuleCat.{u} S)
    {c : ComplexShape ι} (K : HomologicalComplex (ModuleCat.{u} R) c) :
    (((ModuleCat.extendScalars f) ⋙ (curriedTensor (ModuleCat S)).obj M ⋙
        (ModuleCat.restrictScalars.{u} f)).mapHomologicalComplex c).obj K ≅
      (((curriedTensor (ModuleCat R)).obj
        ((ModuleCat.restrictScalars f).obj M)).mapHomologicalComplex c).obj K :=
  (tensorExtendComplexNatIso f M c).app K

/-- The restricted tensor bicomplex underlying `L ⊗[S] (S ⊗[R] K)`. -/
abbrev tensorExtendBicomplexSource
    (f : R →+* S) (L : CochainComplex (ModuleCat.{u} S) ℤ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    HomologicalComplex₂ (ModuleCat.{u} R) (up ℤ) (up ℤ) :=
  (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).mapHomologicalComplex
    (up ℤ)).obj
      ((((curriedTensor (ModuleCat S)).mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj
        L).obj (((ModuleCat.extendScalars f).mapHomologicalComplex (up ℤ)).obj K))

/-- The tensor bicomplex underlying `L|_R ⊗[R] K`. -/
abbrev tensorExtendBicomplexTarget
    (f : R →+* S) (L : CochainComplex (ModuleCat.{u} S) ℤ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    HomologicalComplex₂ (ModuleCat.{u} R) (up ℤ) (up ℤ) :=
  ((((curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj
    (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).obj L)).obj K)

/-- The columnwise projection formulas commute with the outer differential of the tensor
bicomplex. -/
theorem tensorExtendBicomplexIso_outer_comm
    (f : R →+* S) (L : CochainComplex (ModuleCat.{u} S) ℤ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (q q' : ℤ) (_hq : (up ℤ).Rel q q') :
    (tensorExtendComplexIso f (L.X q) K).hom ≫
        (tensorExtendBicomplexTarget f L K).d q q' =
      (tensorExtendBicomplexSource f L K).d q q' ≫
        (tensorExtendComplexIso f (L.X q') K).hom := sorry

/-- The cochain tensor bicomplexes in the change-of-rings projection formula are canonically
isomorphic before totalization. -/
@[stacks 064M "bicomplex change-of-rings projection formula"]
noncomputable def tensorExtendBicomplexIso
    (f : R →+* S) (L : CochainComplex (ModuleCat.{u} S) ℤ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorExtendBicomplexSource f L K ≅ tensorExtendBicomplexTarget f L K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q : ℤ ↦ tensorExtendComplexIso f (L.X q) K)
    (tensorExtendBicomplexIso_outer_comm f L K)

/-- Restriction of scalars applied after totalizing a cochain bicomplex. -/
abbrev mapTotalSource
    (f : R →+* S)
    (B : HomologicalComplex₂ (ModuleCat.{u} S) (up ℤ) (up ℤ)) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  ((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).obj
    (HomologicalComplex₂.total B (up ℤ))

/-- Totalization after restricting every term of a cochain bicomplex. -/
abbrev mapTotalTarget
    (f : R →+* S)
    (B : HomologicalComplex₂ (ModuleCat.{u} S) (up ℤ) (up ℤ)) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  HomologicalComplex₂.total
    ((((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).mapHomologicalComplex
      (up ℤ)).obj B) (up ℤ)

/-- The degreewise coproduct comparison between `mapTotalTarget` and `mapTotalSource`. -/
noncomputable def mapTotalComponentIso
    (f : R →+* S)
    (B : HomologicalComplex₂ (ModuleCat.{u} S) (up ℤ) (up ℤ)) (n : ℤ) :
    (mapTotalTarget f B).X n ≅ (mapTotalSource f B).X n :=
  (PreservesCoproduct.iso (ModuleCat.restrictScalars.{u} f)
    (B.toGradedObject.mapObjFun (ComplexShape.π (up ℤ) (up ℤ) (up ℤ)) n)).symm

/-- The degreewise coproduct comparison intertwines the total differentials. -/
theorem mapTotalComponentIso_hom_naturality
    (f : R →+* S)
    (B : HomologicalComplex₂ (ModuleCat.{u} S) (up ℤ) (up ℤ))
    (i j : ℤ) (hij : (up ℤ).Rel i j) :
    (mapTotalComponentIso f B i).hom ≫ (mapTotalSource f B).d i j =
      (mapTotalTarget f B).d i j ≫ (mapTotalComponentIso f B j).hom := sorry

/-- Restriction of scalars commutes explicitly with the coproduct totalization of an unbounded
cochain bicomplex. -/
@[stacks 064M "restriction of scalars commutes with cochain totalization"]
noncomputable def mapTotalIso
    (f : R →+* S)
    (B : HomologicalComplex₂ (ModuleCat.{u} S) (up ℤ) (up ℤ)) :
    mapTotalSource f B ≅ mapTotalTarget f B :=
  (HomologicalComplex.Hom.isoOfComponents (mapTotalComponentIso f B)
    (mapTotalComponentIso_hom_naturality f B)).symm

/-- The unbounded cochain change-of-rings projection formula
`(L ⊗[S] (S ⊗[R] K))|_R ≅ L|_R ⊗[R] K`. -/
@[stacks 064M "cochain change-of-rings projection formula"]
noncomputable def tensorObjExtendIso
    (f : R →+* S) (L : CochainComplex (ModuleCat.{u} S) ℤ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).obj
        (HomologicalComplex.tensorObj L
          (((ModuleCat.extendScalars f).mapHomologicalComplex (up ℤ)).obj K)) ≅
      HomologicalComplex.tensorObj
        (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).obj L) K :=
  mapTotalIso f
      ((((curriedTensor (ModuleCat S)).mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj
        L).obj (((ModuleCat.extendScalars f).mapHomologicalComplex (up ℤ)).obj K)) ≪≫
    HomologicalComplex₂.total.mapIso (tensorExtendBicomplexIso f L K) (up ℤ)

end ModuleCat.RestrictScalars
