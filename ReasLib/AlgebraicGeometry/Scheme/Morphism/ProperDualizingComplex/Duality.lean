/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Shift
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.DerivedCategory.Ext.TStructure
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Equiv

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

/-- Derived global cohomology over the ground field in degree `i`, represented as degree-zero
homology after shifting the input by `i`. -/
noncomputable def cohomologyOverField
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (K : DerivedQCoh X) (i : ℤ) : ModuleCat.{u} k :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
    ((affineGlobalSections (CommRingCat.of k)).obj ((pushforwardCohomologyIn f).obj (K⟦i⟧)))

/-- `cohomologyOverField` is the homology of affine derived global sections after proper
pushforward. -/
theorem cohomologyOverField_def
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (K : DerivedQCoh X) (i : ℤ) :
    cohomologyOverField f K i =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
        ((affineGlobalSections (CommRingCat.of k)).obj
          ((pushforwardCohomologyIn f).obj (K⟦i⟧))) :=
  rfl

/-- The map on proper cohomology induced by a morphism of derived quasicoherent objects. -/
noncomputable def cohomologyOverFieldMap
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    {K L : DerivedQCoh X} (a : K ⟶ L) (i : ℤ) :
    cohomologyOverField f K i ⟶ cohomologyOverField f L i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
    ((affineGlobalSections (CommRingCat.of k)).map
      ((pushforwardCohomologyIn f).map ((shiftFunctor (DerivedQCoh X) i).map a)))

/-- The canonical copy of the ground field in the affine derived model of its spectrum. -/
noncomputable def fieldObject (k : Type u) [Field k] : ModuleCat.{u} k :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
    ((affineGlobalSections (CommRingCat.of k)).obj
      (structureSheaf (Spec (CommRingCat.of k))))

/-- The ground-field object is degree-zero homology of the derived structure sheaf of its
spectrum. -/
theorem fieldObject_def (k : Type u) [Field k] :
    fieldObject k =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
        ((affineGlobalSections (CommRingCat.of k)).obj
          (structureSheaf (Spec (CommRingCat.of k)))) :=
  rfl

/-- The affine-derived ground-field object represents the usual rank-one module over `k`. -/
theorem fieldObject_isomorphic_field (k : Type u) [Field k] :
    IsIsomorphic (fieldObject k) (ModuleCat.of k k) := sorry

/-- The canonical map from derived `Ext` into the dual of proper cohomology over the field.
The target uses the canonical affine-derived model `fieldObject k` of `k`. -/
noncomputable def extComparison
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) (K : DerivedQCoh X) :
    Ext⁽i⁾(K, properDualizingComplex f) →
      (cohomologyOverField f K (-i) ⟶ fieldObject k) :=
  fun g ↦
    let h := ((Adjunction.ofIsLeftAdjoint (pushforwardCohomologyIn f)).homEquiv
      (K⟦-i⟧) (structureSheaf (Spec (CommRingCat.of k)))).symm
        (ShiftedHom.sourceShiftEquiv K (properDualizingComplex f) i g)
    DerivedCategory.ShiftedHom.Boundary.toHomology
      ((affineGlobalSections (CommRingCat.of k)).obj
        ((pushforwardCohomologyIn f).obj (K⟦-i⟧)))
      ((affineGlobalSections (CommRingCat.of k)).obj
        (structureSheaf (Spec (CommRingCat.of k)))) 0 0
      (ShiftedHom.mk₀ 0 rfl
        ((affineGlobalSections (CommRingCat.of k)).map h))

/-- Evaluation of `extComparison` is the shifted adjunction map, followed by affine derived
global sections and the canonical boundary homology map. -/
theorem extComparison_app
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) (K : DerivedQCoh X) (g : Ext⁽i⁾(K, properDualizingComplex f)) :
    extComparison f i K g =
      let h := ((Adjunction.ofIsLeftAdjoint (pushforwardCohomologyIn f)).homEquiv
        (K⟦-i⟧) (structureSheaf (Spec (CommRingCat.of k)))).symm
          (ShiftedHom.sourceShiftEquiv K (properDualizingComplex f) i g)
      DerivedCategory.ShiftedHom.Boundary.toHomology
        ((affineGlobalSections (CommRingCat.of k)).obj
          ((pushforwardCohomologyIn f).obj (K⟦-i⟧)))
        ((affineGlobalSections (CommRingCat.of k)).obj
          (structureSheaf (Spec (CommRingCat.of k)))) 0 0
        (ShiftedHom.mk₀ 0 rfl
          ((affineGlobalSections (CommRingCat.of k)).map h)) :=
  rfl

/-- Contravariant naturality of the proper duality comparison in the derived quasicoherent
object. -/
theorem extComparison_naturality
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) {K L : DerivedQCoh X} (a : K ⟶ L)
    (g : Ext⁽i⁾(L, properDualizingComplex f)) :
    extComparison f i K (a ≫ g) =
      cohomologyOverFieldMap f a (-i) ≫
        extComparison f i L g := sorry

/-- Reindexing a shifted source gives the canonical map from
`Ext⁽i⁾(K⟦n⟧, properDualizingComplex f)` to
`Ext⁽i - n⁾(K, properDualizingComplex f)`. -/
noncomputable def extSourceShift
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i n : ℤ) (K : DerivedQCoh X) :
    Ext⁽i⁾(K⟦n⟧, properDualizingComplex f) →
      Ext⁽i - n⁾(K, properDualizingComplex f) :=
  fun g ↦
    (ShiftedHom.sourceShiftEquiv K (properDualizingComplex f) (i - n)).symm
      ((shiftFunctorAdd' (DerivedQCoh X) n (-i) (-(i - n))
          ((sub_eq_add_neg n i).symm.trans (neg_sub i n).symm)).hom.app K ≫
        ShiftedHom.sourceShiftEquiv (K⟦n⟧) (properDualizingComplex f) i g)

/-- Proper cohomology of a shifted object in degree `-i` is canonically identified with
proper cohomology of the original object in degree `-(i - n)`. -/
noncomputable def cohomologyShiftIso
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i n : ℤ) (K : DerivedQCoh X) :
    cohomologyOverField f (K⟦n⟧) (-i) ≅
      cohomologyOverField f K (-(i - n)) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).mapIso
    ((affineGlobalSections (CommRingCat.of k)).mapIso
      ((pushforwardCohomologyIn f).mapIso
        ((shiftFunctorAdd' (DerivedQCoh X) n (-i) (-(i - n))
          ((sub_eq_add_neg n i).symm.trans (neg_sub i n).symm)).symm.app K)))

/-- A quasicoherent module placed in degree zero has quasicoherent cohomology. -/
theorem moduleObject_mem {X : Scheme.{u}} (F : QCoh X) :
    Scheme.ModuleDerived.quasicoherentProperty X
      ((DerivedCategory.singleFunctor X.toRingedSpace.Modules 0).obj
        ((QCoh.toRingedSpace X).obj F).obj) := sorry

/-- A quasicoherent module regarded as a derived quasicoherent object in degree zero. -/
noncomputable def moduleObject {X : Scheme.{u}} (F : QCoh X) : DerivedQCoh X :=
  ⟨(DerivedCategory.singleFunctor X.toRingedSpace.Modules 0).obj
      ((QCoh.toRingedSpace X).obj F).obj,
    moduleObject_mem F⟩

/-- The morphism between degree-zero derived objects induced by a morphism of quasicoherent
modules. -/
noncomputable def moduleObjectMap {X : Scheme.{u}} {F G : QCoh X} (a : F ⟶ G) :
    moduleObject F ⟶ moduleObject G :=
  ObjectProperty.homMk
    ((DerivedCategory.singleFunctor X.toRingedSpace.Modules 0).map
      ((QCoh.toRingedSpace X).map a).hom)

/-- After forgetting quasicoherent cohomology, `moduleObjectMap` is the degree-zero derived
map induced by the original quasicoherent-module morphism. -/
theorem moduleObjectMap_obj {X : Scheme.{u}} {F G : QCoh X} (a : F ⟶ G) :
    (DerivedQCoh.inclusion X).map (moduleObjectMap a) =
      (DerivedCategory.singleFunctor X.toRingedSpace.Modules 0).map
        ((QCoh.toRingedSpace X).map a).hom :=
  rfl

/-- The canonical boundary map from the relevant derived `Ext` group to morphisms from a
quasicoherent module into the proper dualizing module. -/
noncomputable def moduleBoundary
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (F : QCoh X) :
    Ext⁽-(dimensionIndex f : ℤ)⁾(moduleObject F, properDualizingComplex f) →
      (((QCoh.toRingedSpace X).obj F).obj ⟶ dualizingModule f) :=
  fun g ↦
    let degreeEq : -(dimensionIndex f : ℤ) = -(dimensionIndex f : ℤ) - 0 :=
      (Int.sub_zero _).symm
    let g' : ShiftedHom (moduleObject F).obj (properDualizingComplex f).obj
        (-(dimensionIndex f : ℤ) - 0) :=
      ShiftedHom.map g (DerivedQCoh.inclusion X) ≫
        eqToHom (congrArg
          (fun n : ℤ ↦ (properDualizingComplex f).obj⟦n⟧) degreeEq)
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
        X.toRingedSpace.Modules 0).inv.app ((QCoh.toRingedSpace X).obj F).obj ≫
      DerivedCategory.ShiftedHom.Boundary.toHomology
        (moduleObject F).obj (properDualizingComplex f).obj 0
        (-(dimensionIndex f : ℤ)) g'

/-- Evaluation of `moduleBoundary` is the canonical cohomological boundary map after forgetting
to ambient derived modules. -/
theorem moduleBoundary_app
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (F : QCoh X)
    (g : Ext⁽-(dimensionIndex f : ℤ)⁾(moduleObject F, properDualizingComplex f)) :
    moduleBoundary f F g =
      let degreeEq : -(dimensionIndex f : ℤ) = -(dimensionIndex f : ℤ) - 0 :=
        (Int.sub_zero _).symm
      let g' : ShiftedHom (moduleObject F).obj (properDualizingComplex f).obj
          (-(dimensionIndex f : ℤ) - 0) :=
        ShiftedHom.map g (DerivedQCoh.inclusion X) ≫
          eqToHom (congrArg
            (fun n : ℤ ↦ (properDualizingComplex f).obj⟦n⟧) degreeEq)
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
          X.toRingedSpace.Modules 0).inv.app ((QCoh.toRingedSpace X).obj F).obj ≫
        DerivedCategory.ShiftedHom.Boundary.toHomology
          (moduleObject F).obj (properDualizingComplex f).obj 0
          (-(dimensionIndex f : ℤ)) g' :=
  rfl

/-- Contravariant naturality of the boundary comparison for morphisms of quasicoherent
modules. -/
theorem moduleBoundary_naturality
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    {F G : QCoh X} (a : F ⟶ G)
    (g : Ext⁽-(dimensionIndex f : ℤ)⁾(moduleObject G, properDualizingComplex f)) :
    moduleBoundary f F (moduleObjectMap a ≫ g) =
      ((QCoh.toRingedSpace X).map a).hom ≫ moduleBoundary f G g := sorry

/-- The boundary comparison between bottom-degree derived `Ext` and morphisms into the
dualizing module is bijective. -/
theorem moduleBoundary_bijective
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (F : QCoh X) :
    Function.Bijective (moduleBoundary f F) := sorry

/-- The direct comparison from morphisms into the dualizing module to the ground-field dual
of top-degree proper cohomology. The inverse image under `moduleBoundary` is selected by
`Function.invFun`; `moduleDualityComparison_moduleBoundary` makes this choice canonical on
the image of the boundary map. -/
noncomputable def moduleDualityComparison
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (F : QCoh X) :
    (((QCoh.toRingedSpace X).obj F).obj ⟶ dualizingModule f) →
      (cohomologyOverField f (moduleObject F) (dimensionIndex f) ⟶ fieldObject k) :=
  fun g ↦
    eqToHom (congrArg (cohomologyOverField f (moduleObject F))
      (Int.neg_neg (dimensionIndex f : ℤ)).symm) ≫
      extComparison f (-(dimensionIndex f : ℤ)) (moduleObject F)
        (Function.invFun (moduleBoundary f F) g)

/-- On an element produced by `moduleBoundary`, the direct module-duality comparison is the
derived `Ext` comparison in degree `-dimensionIndex f`, with the canonical degree transport. -/
theorem moduleDualityComparison_moduleBoundary
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (F : QCoh X)
    (g : Ext⁽-(dimensionIndex f : ℤ)⁾(moduleObject F, properDualizingComplex f)) :
    moduleDualityComparison f F (moduleBoundary f F g) =
      eqToHom (congrArg (cohomologyOverField f (moduleObject F))
        (Int.neg_neg (dimensionIndex f : ℤ)).symm) ≫
        extComparison f (-(dimensionIndex f : ℤ)) (moduleObject F) g := sorry

/-- Contravariant naturality of the direct module-duality comparison for quasicoherent-module
morphisms. -/
theorem moduleDualityComparison_naturality
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    {F G : QCoh X} (a : F ⟶ G)
    (g : ((QCoh.toRingedSpace X).obj G).obj ⟶ dualizingModule f) :
    moduleDualityComparison f F (((QCoh.toRingedSpace X).map a).hom ≫ g) =
      cohomologyOverFieldMap f (moduleObjectMap a) (dimensionIndex f) ≫
        moduleDualityComparison f G g := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex
