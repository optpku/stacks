/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Duality
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Properties
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.DualizingModule
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Module.CohenMacaulay
public import ReasLib.Topology.KrullDimension.Equidimensional
public import ReasLib.CategoryTheory.DerivedCategory.Concentrated.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

/-- The dimension index of the proper dualizing module agrees with the specified
equidimensional dimension. -/
theorem dimensionIndex_eq_of_topologicalKrullDim_eq
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (h_dimension : topologicalKrullDim X = d) :
    dimensionIndex f = d := sorry

/-- For a proper Cohen–Macaulay equidimensional scheme of dimension `d`, its proper
dualizing complex is concentrated in degree `-d`. -/
theorem properDualizingComplex_concentrated
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Scheme.CohenMacaulay X] [TopologicalSpace.EquidimensionalSpace X]
    (d : ℕ) (h_dimension : topologicalKrullDim X = d) :
    DerivedCategory.concentrated X.toRingedSpace.Modules (-(d : ℤ))
      (properDualizingComplex f).obj := sorry

/-- The dualizing module, bundled as a quasicoherent module. -/
noncomputable def dualizingModuleQCoh
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] : QCoh X :=
  ⟨dualizingModule f, inferInstance⟩

/-- The underlying module of `dualizingModuleQCoh f` is `dualizingModule f`. -/
theorem dualizingModuleQCoh_obj
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    (dualizingModuleQCoh f).obj = dualizingModule f := rfl

/-- The ambient derived-module isomorphism identifying the proper dualizing complex with
the degree-zero dualizing module shifted by `d`. -/
noncomputable def dualizingModuleShiftIsoObj
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (d : ℕ) (h_index : dimensionIndex f = d)
    (h_concentrated : DerivedCategory.concentrated X.toRingedSpace.Modules (-(d : ℤ))
      (properDualizingComplex f).obj) :
    (properDualizingComplex f).obj ≅
      ((moduleObject (dualizingModuleQCoh f))⟦(d : ℤ)⟧).obj :=
  DerivedCategory.Concentrated.objIso X.toRingedSpace.Modules (-(d : ℤ))
      ⟨(properDualizingComplex f).obj, h_concentrated⟩ ≪≫
    (DerivedCategory.singleFunctor X.toRingedSpace.Modules (-(d : ℤ))).mapIso
      (eqToIso (congrArg (fun n : ℕ ↦
        cohomologySheaf (properDualizingComplex f).obj (-(n : ℤ))) h_index.symm)) ≪≫
    ((DerivedCategory.singleFunctors X.toRingedSpace.Modules).shiftIso
      (d : ℤ) (-(d : ℤ)) 0
      (add_neg_cancel (d : ℤ))).symm.app (dualizingModule f) ≪≫
    ((DerivedQCoh.inclusion X).commShiftIso (d : ℤ)).symm.app
      (moduleObject (dualizingModuleQCoh f))

/-- The proper dualizing complex as the shifted degree-zero object associated to its
dualizing module.  The proof inputs affect only membership in the concentrated subcategory
and the identification of the dimension index. -/
noncomputable def dualizingModuleShiftIso
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (d : ℕ) (h_index : dimensionIndex f = d)
    (h_concentrated : DerivedCategory.concentrated X.toRingedSpace.Modules (-(d : ℤ))
      (properDualizingComplex f).obj) :
    properDualizingComplex f ≅
      (moduleObject (dualizingModuleQCoh f))⟦(d : ℤ)⟧ :=
  (Scheme.ModuleDerived.quasicoherentProperty X).isoMk
    (dualizingModuleShiftIsoObj f d h_index h_concentrated)

/-- After forgetting quasicoherence, `dualizingModuleShiftIso` is the canonical
concentrated-object isomorphism `dualizingModuleShiftIsoObj`. -/
theorem dualizingModuleShiftIso_obj
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (d : ℕ) (h_index : dimensionIndex f = d)
    (h_concentrated : DerivedCategory.concentrated X.toRingedSpace.Modules (-(d : ℤ))
      (properDualizingComplex f).obj) :
    (DerivedQCoh.inclusion X).mapIso
        (dualizingModuleShiftIso f d h_index h_concentrated) =
      dualizingModuleShiftIsoObj f d h_index h_concentrated := rfl

/-- The bottom cohomology of the proper dualizing complex is a dualizing module in
degree `-d` when `X` is Cohen–Macaulay and equidimensional of dimension `d`. -/
theorem isDualizingModule
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Scheme.CohenMacaulay X] [TopologicalSpace.EquidimensionalSpace X]
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (d : ℕ) (h_dimension : topologicalKrullDim X = d) :
    RingedSpace.ModuleDerived.IsDualizingModule (properDualizingComplex f).obj H (-(d : ℤ))
      (dualizingModule f) := sorry

/-- The coherent dualizing module of a proper Cohen–Macaulay equidimensional scheme is
Cohen–Macaulay. -/
instance dualizingModule_cohenMacaulay
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Scheme.CohenMacaulay X] [TopologicalSpace.EquidimensionalSpace X] :
    Scheme.Modules.CohenMacaulay (dualizingModule f) := sorry

/-- The support of the dualizing module of a proper Cohen–Macaulay equidimensional scheme
is all of `X`. -/
theorem support_eq_univ
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Scheme.CohenMacaulay X] [TopologicalSpace.EquidimensionalSpace X] :
    RingedSpace.moduleSupport (dualizingModule f) = Set.univ := sorry

/-- The Serre comparison from derived `Ext` into the field dual of proper cohomology,
after identifying the proper dualizing complex with the dualizing module shifted by `d`. -/
noncomputable def serreComparison
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (d : ℕ) (h_index : dimensionIndex f = d)
    (h_concentrated : DerivedCategory.concentrated X.toRingedSpace.Modules (-(d : ℤ))
      (properDualizingComplex f).obj)
    (i : ℤ) (K : DerivedQCoh X) :
    Ext⁽i⁾(K, (moduleObject (dualizingModuleQCoh f))⟦(d : ℤ)⟧) →
      (cohomologyOverField f K (-i) ⟶ fieldObject k) :=
  fun g ↦ extComparison f i K
    (g ≫ (dualizingModuleShiftIso f d h_index h_concentrated).inv⟦i⟧')

/-- Evaluation of `serreComparison` is postcomposition with the inverse shifted-module
identification followed by `extComparison`. -/
theorem serreComparison_apply
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (d : ℕ) (h_index : dimensionIndex f = d)
    (h_concentrated : DerivedCategory.concentrated X.toRingedSpace.Modules (-(d : ℤ))
      (properDualizingComplex f).obj)
    (i : ℤ) (K : DerivedQCoh X)
    (g : Ext⁽i⁾(K, (moduleObject (dualizingModuleQCoh f))⟦(d : ℤ)⟧)) :
    serreComparison f d h_index h_concentrated i K g =
      extComparison f i K
        (g ≫ (dualizingModuleShiftIso f d h_index h_concentrated).inv⟦i⟧') := rfl

/-- Derived Serre duality for the dualizing module shifted by `d` is bijective in every
integer degree. -/
theorem serreComparison_bijective
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Scheme.CohenMacaulay X] [TopologicalSpace.EquidimensionalSpace X]
    (d : ℕ) (h_dimension : topologicalKrullDim X = d)
    (i : ℤ) (K : DerivedQCoh X) :
    Function.Bijective (serreComparison f d
      (dimensionIndex_eq_of_topologicalKrullDim_eq f d h_dimension)
      (properDualizingComplex_concentrated f d h_dimension) i K) := sorry

/-- The derived Serre comparison is contravariantly natural in objects of `DerivedQCoh X`. -/
theorem serreComparison_naturality
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Scheme.CohenMacaulay X] [TopologicalSpace.EquidimensionalSpace X]
    (d : ℕ) (h_dimension : topologicalKrullDim X = d)
    (i : ℤ) {K L : DerivedQCoh X} (a : K ⟶ L)
    (g : Ext⁽i⁾(L, (moduleObject (dualizingModuleQCoh f))⟦(d : ℤ)⟧)) :
    serreComparison f d (dimensionIndex_eq_of_topologicalKrullDim_eq f d h_dimension)
        (properDualizingComplex_concentrated f d h_dimension) i K (a ≫ g) =
      cohomologyOverFieldMap f a (-i) ≫
        serreComparison f d (dimensionIndex_eq_of_topologicalKrullDim_eq f d h_dimension)
          (properDualizingComplex_concentrated f d h_dimension) i L g := sorry

/-- Reindexing a shifted source for derived `Ext` into the dualizing module shifted by `d`. -/
noncomputable def serreSourceShift
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (d : ℕ) (i n : ℤ) (K : DerivedQCoh X) :
    Ext⁽i⁾(K⟦n⟧, (moduleObject (dualizingModuleQCoh f))⟦(d : ℤ)⟧) →
      Ext⁽i - n⁾(K, (moduleObject (dualizingModuleQCoh f))⟦(d : ℤ)⟧) :=
  fun g ↦
    (ShiftedHom.sourceShiftEquiv K
      ((moduleObject (dualizingModuleQCoh f))⟦(d : ℤ)⟧) (i - n)).symm
      ((shiftFunctorAdd' (DerivedQCoh X) n (-i) (-(i - n))
          ((sub_eq_add_neg n i).symm.trans (neg_sub i n).symm)).hom.app K ≫
        ShiftedHom.sourceShiftEquiv (K⟦n⟧)
          ((moduleObject (dualizingModuleQCoh f))⟦(d : ℤ)⟧) i g)

/-- Evaluation of `serreSourceShift` is the canonical source-shift equivalence and
shift-addition comparison. -/
theorem serreSourceShift_apply
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (d : ℕ) (i n : ℤ) (K : DerivedQCoh X)
    (g : Ext⁽i⁾(K⟦n⟧, (moduleObject (dualizingModuleQCoh f))⟦(d : ℤ)⟧)) :
    serreSourceShift f d i n K g =
      (ShiftedHom.sourceShiftEquiv K
        ((moduleObject (dualizingModuleQCoh f))⟦(d : ℤ)⟧) (i - n)).symm
        ((shiftFunctorAdd' (DerivedQCoh X) n (-i) (-(i - n))
            ((sub_eq_add_neg n i).symm.trans (neg_sub i n).symm)).hom.app K ≫
          ShiftedHom.sourceShiftEquiv (K⟦n⟧)
            ((moduleObject (dualizingModuleQCoh f))⟦(d : ℤ)⟧) i g) := rfl

/-- The derived Serre comparison is compatible with shifts. -/
theorem serreComparison_shift
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Scheme.CohenMacaulay X] [TopologicalSpace.EquidimensionalSpace X]
    (d : ℕ) (h_dimension : topologicalKrullDim X = d)
    (i n : ℤ) (K : DerivedQCoh X)
    (g : Ext⁽i⁾(K⟦n⟧, (moduleObject (dualizingModuleQCoh f))⟦(d : ℤ)⟧)) :
    (cohomologyShiftIso f i n K).hom ≫
        serreComparison f d (dimensionIndex_eq_of_topologicalKrullDim_eq f d h_dimension)
          (properDualizingComplex_concentrated f d h_dimension) (i - n) K
          (serreSourceShift f d i n K g) =
      serreComparison f d (dimensionIndex_eq_of_topologicalKrullDim_eq f d h_dimension)
        (properDualizingComplex_concentrated f d h_dimension) i (K⟦n⟧) g := sorry

/-- For a distinguished triangle, the derived Serre comparison commutes with its connecting
morphism. -/
theorem serreComparison_distinguishedBoundary
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Scheme.CohenMacaulay X] [TopologicalSpace.EquidimensionalSpace X]
    (d : ℕ) (h_dimension : topologicalKrullDim X = d)
    (T : Pretriangulated.Triangle (DerivedQCoh X))
    (hT : T ∈ distTriang (DerivedQCoh X)) (i : ℤ)
    (g : Ext⁽i⁾(T.obj₁⟦(1 : ℤ)⟧,
      (moduleObject (dualizingModuleQCoh f))⟦(d : ℤ)⟧)) :
    serreComparison f d (dimensionIndex_eq_of_topologicalKrullDim_eq f d h_dimension)
        (properDualizingComplex_concentrated f d h_dimension) i T.obj₃ (T.mor₃ ≫ g) =
      cohomologyOverFieldMap f T.mor₃ (-i) ≫
        serreComparison f d (dimensionIndex_eq_of_topologicalKrullDim_eq f d h_dimension)
          (properDualizingComplex_concentrated f d h_dimension) i
          (T.obj₁⟦(1 : ℤ)⟧) g := sorry

/-- Reindexing module `Ext` from degree `d - i` into the dualizing module to degree `-i`
into the shifted dualizing module. -/
noncomputable def moduleSerreExtEquiv
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (d : ℕ) (i : ℤ) (F : QCoh X) :
    Ext⁽(d : ℤ) - i⁾(moduleObject F, moduleObject (dualizingModuleQCoh f)) ≃
      Ext⁽-i⁾(moduleObject F,
        (moduleObject (dualizingModuleQCoh f))⟦(d : ℤ)⟧) :=
  Iso.homCongr (Iso.refl (moduleObject F))
    ((shiftFunctorAdd' (DerivedQCoh X) (d : ℤ) (-i) ((d : ℤ) - i)
      (sub_eq_add_neg (d : ℤ) i).symm).app (moduleObject (dualizingModuleQCoh f)))

/-- Evaluation of `moduleSerreExtEquiv` is transport along the canonical addition-of-shifts
isomorphism. -/
theorem moduleSerreExtEquiv_apply
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (d : ℕ) (i : ℤ) (F : QCoh X)
    (g : Ext⁽(d : ℤ) - i⁾(moduleObject F, moduleObject (dualizingModuleQCoh f))) :
    moduleSerreExtEquiv f d i F g =
      Iso.homCongr (Iso.refl (moduleObject F))
        ((shiftFunctorAdd' (DerivedQCoh X) (d : ℤ) (-i) ((d : ℤ) - i)
          (sub_eq_add_neg (d : ℤ) i).symm).app
            (moduleObject (dualizingModuleQCoh f))) g := rfl

/-- The module Serre comparison in degree `d - i`, with target the field dual of
degree-`i` proper cohomology. -/
noncomputable def moduleSerreComparison
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (d : ℕ) (h_index : dimensionIndex f = d)
    (h_concentrated : DerivedCategory.concentrated X.toRingedSpace.Modules (-(d : ℤ))
      (properDualizingComplex f).obj)
    (i : ℤ) (F : QCoh X) :
    Ext⁽(d : ℤ) - i⁾(moduleObject F, moduleObject (dualizingModuleQCoh f)) →
      (cohomologyOverField f (moduleObject F) i ⟶ fieldObject k) :=
  fun g ↦
    eqToHom (congrArg (cohomologyOverField f (moduleObject F))
      (Int.neg_neg i).symm) ≫
        serreComparison f d h_index h_concentrated (-i) (moduleObject F)
          (moduleSerreExtEquiv f d i F g)

/-- Evaluation of `moduleSerreComparison` is degree reindexing followed by the derived
Serre comparison, with the canonical double-negation transport on cohomology. -/
theorem moduleSerreComparison_apply
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (d : ℕ) (h_index : dimensionIndex f = d)
    (h_concentrated : DerivedCategory.concentrated X.toRingedSpace.Modules (-(d : ℤ))
      (properDualizingComplex f).obj)
    (i : ℤ) (F : QCoh X)
    (g : Ext⁽(d : ℤ) - i⁾(moduleObject F, moduleObject (dualizingModuleQCoh f))) :
    moduleSerreComparison f d h_index h_concentrated i F g =
      eqToHom (congrArg (cohomologyOverField f (moduleObject F))
        (Int.neg_neg i).symm) ≫
          serreComparison f d h_index h_concentrated (-i) (moduleObject F)
            (moduleSerreExtEquiv f d i F g) := rfl

/-- Module Serre duality is bijective in every integer degree for every quasicoherent
module. -/
theorem moduleSerreComparison_bijective
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Scheme.CohenMacaulay X] [TopologicalSpace.EquidimensionalSpace X]
    (d : ℕ) (h_dimension : topologicalKrullDim X = d)
    (i : ℤ) (F : QCoh X) :
    Function.Bijective (moduleSerreComparison f d
      (dimensionIndex_eq_of_topologicalKrullDim_eq f d h_dimension)
      (properDualizingComplex_concentrated f d h_dimension) i F) := sorry

/-- The module Serre comparison is contravariantly natural in quasicoherent modules. -/
theorem moduleSerreComparison_naturality
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Scheme.CohenMacaulay X] [TopologicalSpace.EquidimensionalSpace X]
    (d : ℕ) (h_dimension : topologicalKrullDim X = d)
    (i : ℤ) {F G : QCoh X} (a : F ⟶ G)
    (g : Ext⁽(d : ℤ) - i⁾(moduleObject G, moduleObject (dualizingModuleQCoh f))) :
    moduleSerreComparison f d
        (dimensionIndex_eq_of_topologicalKrullDim_eq f d h_dimension)
        (properDualizingComplex_concentrated f d h_dimension) i F
        (moduleObjectMap a ≫ g) =
      cohomologyOverFieldMap f (moduleObjectMap a) i ≫
        moduleSerreComparison f d
          (dimensionIndex_eq_of_topologicalKrullDim_eq f d h_dimension)
          (properDualizingComplex_concentrated f d h_dimension) i G g := sorry

end ProperDualizingComplex
end DerivedQCoh
end Scheme
end AlgebraicGeometry
