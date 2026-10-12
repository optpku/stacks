/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve
import StacksCheckRecall

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

/- Lemma 53.4.1 (1) -/
@[stacks 0BS2] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.isDualizing_of_dimension_le_one :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1),
    @Scheme.IsDualizingComplex X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (properDualizingComplex X.hom).obj)

/- Lemma 53.4.1 (2) -/
@[stacks 0BS2] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.cohomology_isZero_of_ne_neg_one_of_ne_zero :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1) (i : ℤ)
    (hi_neg_one : i ≠ -1) (hi_zero : i ≠ 0),
    IsZero (RingedSpace.ModuleDerived.cohomologySheaf
      (properDualizingComplex X.hom).obj i))

/- Lemma 53.4.1 (3) -/
@[stacks 0BS2] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveDualizingModule_isCoherent :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1),
    (curveDualizingModule X.hom).IsCoherent)

/- Lemma 53.4.1 (4) -/
@[stacks 0BS2] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveDualizingModule_cohenMacaulay :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1),
    ∀ x : X.left, x ∈ RingedSpace.moduleSupport (curveDualizingModule X.hom) →
      @Module.CohenMacaulay (SchemeOverField.stalkRing X x)
        inferInstance inferInstance
        (@instIsNoetherianRingCarrierStalkCommRingCatPresheafOfIsLocallyNoetherian
          X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom) x)
        (RingedSpace.stalkModuleCat (curveDualizingModule X.hom) x)
        inferInstance inferInstance)

/- Lemma 53.4.1 (5) -/
@[stacks 0BS2] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveDualizingModule_support :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1),
    RingedSpace.moduleSupport (curveDualizingModule X.hom) =
      ⋃ Z : irreducibleComponents X.left,
        ⋃ (_ : topologicalKrullDim Z = 1), (Z : Set X.left))

/- Lemma 53.4.1 (6) -/
@[stacks 0BS2] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.cohomologyStalk_zero_nontrivial_iff :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1)
    (x : X.left) (hx : x ∈ closedPoints X.left),
    Nontrivial (cohomologyStalk (properDualizingComplex X.hom).obj 0 x) ↔
      ringKrullDim (SchemeOverField.stalkRing X x) = 0 ∨
        (ringKrullDim (SchemeOverField.stalkRing X x) = 1 ∧
          ¬ @Module.CohenMacaulay (SchemeOverField.stalkRing X x)
            inferInstance inferInstance
            (@instIsNoetherianRingCarrierStalkCommRingCatPresheafOfIsLocallyNoetherian
              X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom) x)
            (SchemeOverField.stalkRing X x) inferInstance inferInstance))

/- Lemma 53.4.1 (7) -/
@[stacks 0BS2] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveExtComparison_bijective :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1) (i : ℤ) (K : DerivedQCoh X.left),
    Function.Bijective (extComparison X.hom i K))

/- Lemma 53.4.1 (8) -/
@[stacks 0BS2] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveExtComparison_naturality :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1)
    (i : ℤ) {K L : DerivedQCoh X.left} (a : K ⟶ L)
    (g : Ext⁽i⁾(L, properDualizingComplex X.hom)),
    extComparison X.hom i K (a ≫ g) =
      cohomologyOverFieldMap X.hom a (-i) ≫ extComparison X.hom i L g)

/- Lemma 53.4.1 (9) -/
@[stacks 0BS2] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveExtComparison_shift :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1)
    (i n : ℤ) (K : DerivedQCoh X.left)
    (g : Ext⁽i⁾(K⟦n⟧, properDualizingComplex X.hom)),
    (cohomologyShiftIso X.hom i n K).hom ≫
        extComparison X.hom (i - n) K (extSourceShift X.hom i n K g) =
      extComparison X.hom i (K⟦n⟧) g)

/- Lemma 53.4.1 (10) -/
@[stacks 0BS2] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveExtComparison_distinguishedBoundary :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1)
    (T : Pretriangulated.Triangle (DerivedQCoh X.left))
    (hT : T ∈ distTriang (DerivedQCoh X.left)) (i : ℤ)
    (g : Ext⁽i⁾(T.obj₁⟦(1 : ℤ)⟧, properDualizingComplex X.hom)),
    extComparison X.hom i T.obj₃ (T.mor₃ ≫ g) =
      cohomologyOverFieldMap X.hom T.mor₃ (-i) ≫
        extComparison X.hom i (T.obj₁⟦(1 : ℤ)⟧) g)

/- Lemma 53.4.1 (11) -/
@[stacks 0BS2] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveModuleDualityComparison_bijective :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1) (F : QCoh X.left),
    Function.Bijective (curveModuleDualityComparison X.hom F))

/- Lemma 53.4.1 (12) -/
@[stacks 0BS2] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveModuleDualityComparison_naturality :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1)
    {F G : QCoh X.left} (a : F ⟶ G)
    (g : ((QCoh.toRingedSpace X.left).obj G).obj ⟶ curveDualizingModule X.hom),
    curveModuleDualityComparison X.hom F
        (((QCoh.toRingedSpace X.left).map a).hom ≫ g) =
      cohomologyOverFieldMap X.hom (moduleObjectMap a) 1 ≫
        curveModuleDualityComparison X.hom G g)

/- Lemma 53.4.1 (13) -/
@[stacks 0BS2] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveDualizingModule_isomorphic_differentials :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1)
    [SmoothOfRelativeDimension 1 X.hom],
    IsIsomorphic (curveDualizingModule X.hom) Ω[X.hom.toShHom])
end ProperDualizingComplex
end DerivedQCoh
end Scheme
end AlgebraicGeometry
