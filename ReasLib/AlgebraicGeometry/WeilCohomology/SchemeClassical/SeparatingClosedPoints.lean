module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.BaseChange
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.DimensionZero
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.GradedCycleClass
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

@[expose] public section

noncomputable section

universe u v w x y z

namespace WeilCohomology.SchemeClassicalTheory

open AlgebraicGeometry CategoryTheory

variable {k : Type u} [Field k]
variable {F : Type v} [Field F] [CharZero F]
variable {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {H : V → Type x} {CH : V → Type y}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
variable {Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X)}
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
variable [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V},
  (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}

variable (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
  H CH Hgrade CHgrade cyclePullback cyclePushforward)

/-- The point-closure immersion commutes with the structure morphism to
`Spec k`, as required to regard it as a morphism over `k`. -/
theorem pointClosureInclusion_comm (X : V)
    (p : closedPoints (T.scheme.obj X).left) :
    @Scheme.PointClosure.ι (T.scheme.obj X).left p ≫ (T.scheme.obj X).hom =
      (Over.mk (@Scheme.PointClosure.ι (T.scheme.obj X).left p ≫
        (T.scheme.obj X).hom) :
        SchemeOverField k).hom := sorry

/-- The canonical morphism over `Spec k` from the reduced closure of a closed
point to its ambient represented scheme. -/
noncomputable def pointClosureInclusion (X : V)
    (p : closedPoints (T.scheme.obj X).left) :
    Over.mk (@Scheme.PointClosure.ι (T.scheme.obj X).left p ≫
      (T.scheme.obj X).hom) ⟶ T.scheme.obj X :=
  Over.homMk (@Scheme.PointClosure.ι (T.scheme.obj X).left p)
    (T.pointClosureInclusion_comm X p)

/-- The underlying scheme morphism of `pointClosureInclusion` is the canonical
closed immersion of the reduced point closure. -/
theorem pointClosureInclusion_left (X : V)
    (p : closedPoints (T.scheme.obj X).left) :
    (T.pointClosureInclusion X p).left =
      @Scheme.PointClosure.ι (T.scheme.obj X).left p := sorry

/-- An abstract morphism represents the inclusion of a specified closed-point
closure in the realized scheme. -/
def RepresentsClosedPoint {P X : V} (p : closedPoints (T.scheme.obj X).left)
    (f : P ⟶ X)
    (e : T.scheme.obj P ≅
      Over.mk (@Scheme.PointClosure.ι (T.scheme.obj X).left p ≫
        (T.scheme.obj X).hom)) : Prop :=
  T.scheme.map f = e.hom ≫ T.pointClosureInclusion X p

/-- An abstract morphism represents a closed point exactly when its realized
underlying morphism is the chosen point-closure identification followed by the
canonical closed immersion. -/
theorem representsClosedPoint_iff {P X : V}
    (p : closedPoints (T.scheme.obj X).left) (f : P ⟶ X)
    (e : T.scheme.obj P ≅
      Over.mk (@Scheme.PointClosure.ι (T.scheme.obj X).left p ≫
        (T.scheme.obj X).hom)) :
    T.RepresentsClosedPoint p f e ↔
      T.scheme.map f = e.hom ≫ T.pointClosureInclusion X p := sorry

/-- The existence of finitely many separable closed points whose degree-zero
cohomology restriction maps jointly detect classes. -/
def HasSeparatingClosedPoints (X : V) : Prop :=
  ∃ (r : ℕ) (x : Fin r → closedPoints (T.scheme.obj X).left)
    (P : Fin r → V) (f : ∀ i, P i ⟶ X)
    (e : ∀ i, T.scheme.obj (P i) ≅
      Over.mk (@Scheme.PointClosure.ι (T.scheme.obj X).left (x i) ≫
        (T.scheme.obj X).hom)),
    (∀ i, Algebra.IsSeparable k ((T.scheme.obj X).left.residueField (x i))) ∧
      (∀ i, T.RepresentsClosedPoint (x i) (f i) (e i)) ∧
      Function.Injective (fun a : Hgrade X (0, 0) ↦
        fun i ↦ T.degreeZeroPullback (f i) a)

/-- The finite-family specification of `HasSeparatingClosedPoints`. -/
theorem hasSeparatingClosedPoints_iff (X : V) :
    T.HasSeparatingClosedPoints X ↔
      ∃ (r : ℕ) (x : Fin r → closedPoints (T.scheme.obj X).left)
        (P : Fin r → V) (f : ∀ i, P i ⟶ X)
        (e : ∀ i, T.scheme.obj (P i) ≅
          Over.mk (@Scheme.PointClosure.ι (T.scheme.obj X).left (x i) ≫
            (T.scheme.obj X).hom)),
        (∀ i, Algebra.IsSeparable k ((T.scheme.obj X).left.residueField (x i))) ∧
          (∀ i, T.RepresentsClosedPoint (x i) (f i) (e i)) ∧
          Function.Injective (fun a : Hgrade X (0, 0) ↦
            fun i ↦ T.degreeZeroPullback (f i) a) := sorry

/-- Separable closed-point restrictions detect degree-zero cohomology exactly
when pullback from the spectrum of global sections is bijective. -/
theorem hasSeparatingClosedPoints_iff_globalSectionsPullback_bijective
    {K X : V} (s : X ⟶ K)
    (eK : T.scheme.obj K ≅
      Over.mk (Scheme.Hom.globalSectionsSpecMap (T.scheme.obj X).hom))
    (hs : (T.scheme.map s ≫ eK.hom).left = (T.scheme.obj X).left.toSpecΓ) :
    T.HasSeparatingClosedPoints X ↔
      Function.Bijective (T.degreeZeroPullback s) := sorry

/-- When separable closed-point restrictions detect degree-zero classes,
degree-zero cohomology is a finite separable `F`-algebra. -/
theorem degreeZeroFiniteSeparable_of_hasSeparatingClosedPoints
    {X : V} (hX : T.HasSeparatingClosedPoints X) :
    Module.Finite F (Hgrade X (0, 0)) ∧
      @Algebra.IsSeparable F (Hgrade X (0, 0)) inferInstance
        (T.degreeZeroCommRing X).toRing inferInstance := sorry

/-- Degree-zero cohomology acts on a homogeneous piece by graded multiplication,
using the commutative ring structure on the bidegree `(0, 0)` piece. -/
instance moduleHgrade_of_degreeZero (X : V) (i : ℤ × ℤ) :
    Module (Hgrade X (0, 0)) (Hgrade X i) where
  smul a b :=
    ⟨(a : H X) * (b : H X),
      cast (congrArg (fun j => (a : H X) * (b : H X) ∈ Hgrade X j) (zero_add i))
        (SetLike.mul_mem_graded a.2 b.2)⟩
  one_smul b := Subtype.ext (one_mul (b : H X))
  mul_smul a a' b := Subtype.ext (mul_assoc (a : H X) (a' : H X) (b : H X))
  smul_zero a := Subtype.ext (mul_zero (a : H X))
  smul_add a b c := Subtype.ext (mul_add (a : H X) (b : H X) (c : H X))
  add_smul a a' b := Subtype.ext (add_mul (a : H X) (a' : H X) (b : H X))
  zero_smul b := Subtype.ext (zero_mul (b : H X))

/-- For a nonempty equidimensional scheme, separable closed-point restrictions
detect degree-zero classes exactly when closed-point cycle classes span top
cohomology over degree-zero cohomology. -/
theorem hasSeparatingClosedPoints_iff_closedPointClasses_span_eq_top
    {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) :
    T.HasSeparatingClosedPoints X ↔
      @Submodule.span (Hgrade X (0, 0)) (Hgrade X (2 * (d : ℤ), (d : ℤ)))
        (T.degreeZeroCommRing X).toSemiring _
        (moduleHgrade_of_degreeZero X (2 * (d : ℤ), (d : ℤ)))
        (Set.range (fun p : closedPoints (T.scheme.obj X).left ↦
          T.gradedCycleClass X (d : ℤ) (T.closedPointClass hX p))) = ⊤ := sorry

end WeilCohomology.SchemeClassicalTheory
