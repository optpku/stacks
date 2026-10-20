module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Properties
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.RingTheory.CohenMacaulay.Module

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived
open DerivedCategory.ShiftedHom.Boundary
open scoped DerivedExt ENat

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DerivedQCoh
namespace ProperDualizingComplex

/-- The degree-`-1` cohomology sheaf of the proper dualizing complex of a scheme over a
field. -/
noncomputable def curveDualizingModule
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] : X.Modules :=
  RingedSpace.ModuleDerived.cohomologySheaf (properDualizingComplex f).obj (-1)

/-- The curve dualizing module is the degree-`-1` cohomology sheaf of the proper
dualizing complex. -/
theorem curveDualizingModule_eq
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    curveDualizingModule f =
      RingedSpace.ModuleDerived.cohomologySheaf (properDualizingComplex f).obj (-1) := sorry

/-- The canonical boundary map from degree-`-1` derived `Ext` to morphisms into the
curve dualizing module. -/
noncomputable def curveModuleBoundary
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (F : QCoh X) :
    Ext⁽(-1 : ℤ)⁾(moduleObject F, properDualizingComplex f) →
      (((QCoh.toRingedSpace X).obj F).obj ⟶ curveDualizingModule f) :=
  fun g ↦
    let degreeEq : (-1 : ℤ) = -1 - 0 := (Int.sub_zero _).symm
    let g' : ShiftedHom (moduleObject F).obj (properDualizingComplex f).obj
        ((-1 : ℤ) - 0) :=
      ShiftedHom.map g (DerivedQCoh.inclusion X) ≫
        eqToHom (congrArg
          (fun n : ℤ ↦ (properDualizingComplex f).obj⟦n⟧) degreeEq)
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
        X.toRingedSpace.Modules 0).inv.app ((QCoh.toRingedSpace X).obj F).obj ≫
      toHomology (moduleObject F).obj (properDualizingComplex f).obj 0 (-1) g'

/-- Evaluation of `curveModuleBoundary` is the canonical cohomological boundary map
after forgetting to ambient derived modules. -/
theorem curveModuleBoundary_app
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (F : QCoh X)
    (g : Ext⁽(-1 : ℤ)⁾(moduleObject F, properDualizingComplex f)) :
    curveModuleBoundary f F g =
      let degreeEq : (-1 : ℤ) = -1 - 0 := (Int.sub_zero _).symm
      let g' : ShiftedHom (moduleObject F).obj (properDualizingComplex f).obj
          ((-1 : ℤ) - 0) :=
        ShiftedHom.map g (DerivedQCoh.inclusion X) ≫
          eqToHom (congrArg
            (fun n : ℤ ↦ (properDualizingComplex f).obj⟦n⟧) degreeEq)
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
          X.toRingedSpace.Modules 0).inv.app ((QCoh.toRingedSpace X).obj F).obj ≫
        toHomology (moduleObject F).obj (properDualizingComplex f).obj 0 (-1) g' := sorry

/-- In dimension at most one, the boundary map from degree-`-1` derived `Ext` to
morphisms into the curve dualizing module is bijective. -/
theorem curveModuleBoundary_bijective
    {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1) (F : QCoh X.left) :
    Function.Bijective (curveModuleBoundary X.hom F) := sorry

/-- The direct comparison from morphisms into the curve dualizing module to the
ground-field dual of first proper cohomology. -/
noncomputable def curveModuleDualityComparison
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (F : QCoh X) :
    (((QCoh.toRingedSpace X).obj F).obj ⟶ curveDualizingModule f) →
      (cohomologyOverField f (moduleObject F) 1 ⟶ fieldObject k) :=
  fun g ↦
    eqToHom (congrArg (cohomologyOverField f (moduleObject F))
      (Int.neg_neg (1 : ℤ)).symm) ≫
      extComparison f (-1) (moduleObject F)
        (Function.invFun (curveModuleBoundary f F) g)

/-- In dimension at most one, the curve-module comparison on an element produced by
`curveModuleBoundary` is the derived `Ext` comparison in degree `-1`. -/
theorem curveModuleDualityComparison_curveModuleBoundary
    {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1) (F : QCoh X.left)
    (g : Ext⁽(-1 : ℤ)⁾(moduleObject F, properDualizingComplex X.hom)) :
    curveModuleDualityComparison X.hom F (curveModuleBoundary X.hom F g) =
      eqToHom (congrArg (cohomologyOverField X.hom (moduleObject F))
        (Int.neg_neg (1 : ℤ)).symm) ≫
        extComparison X.hom (-1) (moduleObject F) g := sorry

/-- the canonical proper dualizing complex on a proper scheme of
dimension at most one over a field is a dualizing complex. -/
theorem isDualizing_of_dimension_le_one
    {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1) :
    @Scheme.IsDualizingComplex X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (properDualizingComplex X.hom).obj := sorry

/-- the only possibly nonzero cohomology sheaves of the canonical
proper dualizing complex are in degrees `-1` and `0`. -/
theorem cohomology_isZero_of_ne_neg_one_of_ne_zero
    {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1) (i : ℤ)
    (hi_neg_one : i ≠ -1) (hi_zero : i ≠ 0) :
    IsZero (RingedSpace.ModuleDerived.cohomologySheaf
      (properDualizingComplex X.hom).obj i) := sorry

/-- the degree-`-1` cohomology of the canonical proper dualizing
complex is coherent. -/
theorem curveDualizingModule_isCoherent
    {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1) :
    (curveDualizingModule X.hom).IsCoherent := sorry

/-- The degree-`-1` dualizing module on a proper scheme over a field is coherent
when its topological dimension is at most one. -/
instance instCurveDualizingModuleIsCoherent
    {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    [Fact (topologicalKrullDim X.left ≤ 1)] :
    (curveDualizingModule X.hom).IsCoherent :=
  curveDualizingModule_isCoherent X Fact.out

/-- On a proper scheme of dimension at most one over a field, every stalk in the
support of the degree-`-1` dualizing module is Cohen–Macaulay over its local ring. -/
theorem curveDualizingModule_cohenMacaulay
    {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1) :
    ∀ x : X.left, x ∈ RingedSpace.moduleSupport (curveDualizingModule X.hom) →
      @Module.CohenMacaulay (SchemeOverField.stalkRing X x)
        inferInstance inferInstance
        (@instIsNoetherianRingCarrierStalkCommRingCatPresheafOfIsLocallyNoetherian
          X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom) x)
        (RingedSpace.stalkModuleCat (curveDualizingModule X.hom) x)
        inferInstance inferInstance := sorry

/-- the support of the curve dualizing module is the union of the
one-dimensional irreducible components. -/
theorem curveDualizingModule_support
    {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1) :
    RingedSpace.moduleSupport (curveDualizingModule X.hom) =
      ⋃ Z : irreducibleComponents X.left,
        ⋃ (_ : topologicalKrullDim Z = 1), (Z : Set X.left) := sorry

/-- at a closed point, degree-zero cohomology of the proper
dualizing complex is nonzero exactly in local dimension zero or at a non-Cohen–Macaulay
point of local dimension one. -/
theorem cohomologyStalk_zero_nontrivial_iff
    {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1)
    (x : X.left) (hx : x ∈ closedPoints X.left) :
    Nontrivial (cohomologyStalk (properDualizingComplex X.hom).obj 0 x) ↔
      ringKrullDim (SchemeOverField.stalkRing X x) = 0 ∨
        (ringKrullDim (SchemeOverField.stalkRing X x) = 1 ∧
          ¬ @Module.CohenMacaulay (SchemeOverField.stalkRing X x)
            inferInstance inferInstance
            (@instIsNoetherianRingCarrierStalkCommRingCatPresheafOfIsLocallyNoetherian
              X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom) x)
            (SchemeOverField.stalkRing X x) inferInstance inferInstance) := sorry

/-- the canonical comparison identifies derived `Ext` into the
proper dualizing complex with the ground-field dual of oppositely indexed cohomology. -/
theorem curveExtComparison_bijective
    {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1) (i : ℤ) (K : DerivedQCoh X.left) :
    Function.Bijective (extComparison X.hom i K) := sorry

/-- the derived `Ext` comparison is contravariantly functorial in
the quasicoherent complex. -/
theorem curveExtComparison_naturality
    {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1)
    (i : ℤ) {K L : DerivedQCoh X.left} (a : K ⟶ L)
    (g : Ext⁽i⁾(L, properDualizingComplex X.hom)) :
    extComparison X.hom i K (a ≫ g) =
      cohomologyOverFieldMap X.hom a (-i) ≫ extComparison X.hom i L g := sorry

/-- the derived `Ext` comparison is compatible with shifts. -/
theorem curveExtComparison_shift
    {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1)
    (i n : ℤ) (K : DerivedQCoh X.left)
    (g : Ext⁽i⁾(K⟦n⟧, properDualizingComplex X.hom)) :
    (cohomologyShiftIso X.hom i n K).hom ≫
        extComparison X.hom (i - n) K (extSourceShift X.hom i n K g) =
      extComparison X.hom i (K⟦n⟧) g := sorry

/-- the derived `Ext` comparison is compatible with connecting
morphisms of distinguished triangles. -/
theorem curveExtComparison_distinguishedBoundary
    {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1)
    (T : Pretriangulated.Triangle (DerivedQCoh X.left))
    (hT : T ∈ distTriang (DerivedQCoh X.left)) (i : ℤ)
    (g : Ext⁽i⁾(T.obj₁⟦(1 : ℤ)⟧, properDualizingComplex X.hom)) :
    extComparison X.hom i T.obj₃ (T.mor₃ ≫ g) =
      cohomologyOverFieldMap X.hom T.mor₃ (-i) ≫
        extComparison X.hom i (T.obj₁⟦(1 : ℤ)⟧) g := sorry

/-- morphisms from a quasicoherent module to the curve dualizing
module are canonically identified with the ground-field dual of its first cohomology. -/
theorem curveModuleDualityComparison_bijective
    {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1) (F : QCoh X.left) :
    Function.Bijective (curveModuleDualityComparison X.hom F) := sorry

/-- the curve-module duality comparison is contravariantly
functorial in the quasicoherent module. -/
theorem curveModuleDualityComparison_naturality
    {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1)
    {F G : QCoh X.left} (a : F ⟶ G)
    (g : ((QCoh.toRingedSpace X.left).obj G).obj ⟶ curveDualizingModule X.hom) :
    curveModuleDualityComparison X.hom F
        (((QCoh.toRingedSpace X.left).map a).hom ≫ g) =
      cohomologyOverFieldMap X.hom (moduleObjectMap a) 1 ≫
        curveModuleDualityComparison X.hom G g := sorry

/-- if the structure morphism is smooth of relative dimension
one, then the curve dualizing module is isomorphic to the sheaf of relative differentials. -/
theorem curveDualizingModule_isomorphic_differentials
    {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1)
    [SmoothOfRelativeDimension 1 X.hom] :
    IsIsomorphic (curveDualizingModule X.hom) Ω[X.hom.toShHom] := sorry
end ProperDualizingComplex
end DerivedQCoh
end Scheme
end AlgebraicGeometry
