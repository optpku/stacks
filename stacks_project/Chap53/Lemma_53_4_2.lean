/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.CohenMacaulay

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived
open AlgebraicGeometry.Scheme
open Scheme.DerivedQCoh
open ProperDualizingComplex
open scoped DerivedExt

noncomputable section

universe u

section

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  [Scheme.CohenMacaulay X] [EquidimensionalSpace X]
variable (h_dimension : topologicalKrullDim X = 1)
variable [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
  (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
variable (i : ℤ) (K : DerivedQCoh X)

/- Lemma 53.4.2 (1) -/
@[stacks 0BS3] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.isDualizingModule
      f H 1 h_dimension :
    RingedSpace.ModuleDerived.IsDualizingModule
      (properDualizingComplex f).obj H (-(1 : ℤ))
      (dualizingModule f))

/- Lemma 53.4.2 (2) -/
@[stacks 0BS3] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dualizingModule_isCoherent
      f :
    (dualizingModule f).IsCoherent)

/- Lemma 53.4.2 (3) -/
@[stacks 0BS3] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dualizingModule_cohenMacaulay
      f :
    Scheme.Modules.CohenMacaulay (dualizingModule f))

/- Lemma 53.4.2 (4) -/
@[stacks 0BS3] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.support_eq_univ f :
    RingedSpace.moduleSupport (dualizingModule f) = Set.univ)

/- Lemma 53.4.2 (5) -/
@[stacks 0BS3] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.serreComparison_bijective
      f 1 h_dimension i K :
    Function.Bijective
      (serreComparison f 1
        (dimensionIndex_eq_of_topologicalKrullDim_eq f 1 h_dimension)
        (properDualizingComplex_concentrated f 1 h_dimension) i K))

variable {K L : DerivedQCoh X} (a : K ⟶ L)
variable (g : Ext⁽i⁾(L, (moduleObject (dualizingModuleQCoh f))⟦(1 : ℤ)⟧))

/- Lemma 53.4.2 (6) -/
@[stacks 0BS3] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.serreComparison_naturality
      f 1 h_dimension i a g :
    serreComparison f 1
        (dimensionIndex_eq_of_topologicalKrullDim_eq f 1 h_dimension)
        (properDualizingComplex_concentrated f 1 h_dimension) i K (a ≫ g) =
      cohomologyOverFieldMap f a (-i) ≫
        serreComparison f 1
          (dimensionIndex_eq_of_topologicalKrullDim_eq f 1 h_dimension)
          (properDualizingComplex_concentrated f 1 h_dimension) i L g)

variable (n : ℤ) (KShift : DerivedQCoh X)
variable
  (g_shift : Ext⁽i⁾(KShift⟦n⟧,
    (moduleObject (dualizingModuleQCoh f))⟦(1 : ℤ)⟧))

/- Lemma 53.4.2 (7) -/
@[stacks 0BS3] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.serreComparison_shift
      f 1 h_dimension i n KShift g_shift :
    (cohomologyShiftIso f i n KShift).hom ≫
        serreComparison f 1
          (dimensionIndex_eq_of_topologicalKrullDim_eq f 1 h_dimension)
          (properDualizingComplex_concentrated f 1 h_dimension) (i - n) KShift
          (serreSourceShift f 1 i n KShift g_shift) =
      serreComparison f 1
        (dimensionIndex_eq_of_topologicalKrullDim_eq f 1 h_dimension)
        (properDualizingComplex_concentrated f 1 h_dimension) i (KShift⟦n⟧) g_shift)

variable (F : QCoh X)

/- Lemma 53.4.2 (8) -/
@[stacks 0BS3] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.moduleSerreComparison_bijective
      f 1 h_dimension i F :
    Function.Bijective
      (moduleSerreComparison f 1
        (dimensionIndex_eq_of_topologicalKrullDim_eq f 1 h_dimension)
        (properDualizingComplex_concentrated f 1 h_dimension) i F))

variable {F G : QCoh X} (moduleMap : F ⟶ G)
variable
  (module_g : Ext⁽(1 : ℤ) - i⁾(moduleObject G,
    moduleObject (dualizingModuleQCoh f)))

/- Lemma 53.4.2 (9) -/
@[stacks 0BS3] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.moduleSerreComparison_naturality
      f 1 h_dimension i moduleMap module_g :
    moduleSerreComparison f 1
        (dimensionIndex_eq_of_topologicalKrullDim_eq f 1 h_dimension)
        (properDualizingComplex_concentrated f 1 h_dimension) i F
        (moduleObjectMap moduleMap ≫ module_g) =
      cohomologyOverFieldMap f (moduleObjectMap moduleMap) i ≫
        moduleSerreComparison f 1
          (dimensionIndex_eq_of_topologicalKrullDim_eq f 1 h_dimension)
          (properDualizingComplex_concentrated f 1 h_dimension) i G module_g)

end
