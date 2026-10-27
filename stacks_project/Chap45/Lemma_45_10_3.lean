/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.Degree
import StacksCheckRecall

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
variable {Hgrade : ∀ X, ℤ → Submodule F (H X)}
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
variable [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V},
  (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}

/-- The theory supplies the smooth structure used in relative dimension functions. -/
local instance facadeDegreeRepresentedSmooth
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward) (X : V) :
    Smooth (T.scheme.obj X).hom := T.smooth X

/- Lemma 45.10.3: for a nonempty equidimensional smooth projective scheme,
integration after the top-degree cycle-class map is the degree of the corresponding
zero-cycle class, cast from `ℤ` to `F`. -/
@[stacks 0FHR] #check
  (WeilCohomology.SchemeClassicalTheory.integral_cycleClass_eq_degree :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d)
      (chowTopEquiv : CHgrade X (d : ℤ) ≃+
        @ChowGroup (T.scheme.obj X).left
          (@LocallyOfFiniteType.isLocallyNoetherian _ _ (T.scheme.obj X).hom
            (T.projective X).isProper.toLocallyOfFiniteType inferInstance)
          ((T.scheme.obj X).hom.relativeDimensionFunction
            (fun _ : Spec (CommRingCat.of k) ↦ 0))
          (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction _ _
            (T.scheme.obj X).hom inferInstance
            (T.projective X).isProper.toLocallyOfFiniteType
            (fun _ : Spec (CommRingCat.of k) ↦ 0) inferInstance) 0)
      (chowTopEquiv_closedPointClass : ∀ x : closedPoints (T.scheme.obj X).left,
        Algebra.IsSeparable k ((T.scheme.obj X).left.residueField x) →
          chowTopEquiv (T.closedPointClass hX x) =
            @AlgebraicGeometry.chowClass (T.scheme.obj X).left
              (@LocallyOfFiniteType.isLocallyNoetherian _ _ (T.scheme.obj X).hom
                (T.projective X).isProper.toLocallyOfFiniteType inferInstance)
              ((T.scheme.obj X).hom.relativeDimensionFunction
                (fun _ : Spec (CommRingCat.of k) ↦ 0))
              (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction _ _
                (T.scheme.obj X).hom inferInstance
                (T.projective X).isProper.toLocallyOfFiniteType
                (fun _ : Spec (CommRingCat.of k) ↦ 0) inferInstance) 0
              (CycleGroup.point
                ((T.scheme.obj X).hom.relativeDimensionFunction
                  (fun _ : Spec (CommRingCat.of k) ↦ 0)) 0 x
                (@SchemeOverField.closedPoint_relativeDimensionFunction_eq_zero k _
                  (T.scheme.obj X) (T.projective X).isProper.toLocallyOfFiniteType x)))
      (alpha : CHgrade X (d : ℤ)),
      T.integral hX (T.cycleClass X alpha) =
        (@ChowGroup.degree k _ (T.scheme.obj X) (T.projective X).isProper
          (chowTopEquiv alpha) : F))

/- The equivalent additive-map formulation of Lemma 45.10.3. -/
#check
  (WeilCohomology.SchemeClassicalTheory.integral_comp_cycleClass_eq_degree :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d)
      (chowTopEquiv : CHgrade X (d : ℤ) ≃+
        @ChowGroup (T.scheme.obj X).left
          (@LocallyOfFiniteType.isLocallyNoetherian _ _ (T.scheme.obj X).hom
            (T.projective X).isProper.toLocallyOfFiniteType inferInstance)
          ((T.scheme.obj X).hom.relativeDimensionFunction
            (fun _ : Spec (CommRingCat.of k) ↦ 0))
          (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction _ _
            (T.scheme.obj X).hom inferInstance
            (T.projective X).isProper.toLocallyOfFiniteType
            (fun _ : Spec (CommRingCat.of k) ↦ 0) inferInstance) 0)
      (chowTopEquiv_closedPointClass : ∀ x : closedPoints (T.scheme.obj X).left,
        Algebra.IsSeparable k ((T.scheme.obj X).left.residueField x) →
          chowTopEquiv (T.closedPointClass hX x) =
            @AlgebraicGeometry.chowClass (T.scheme.obj X).left
              (@LocallyOfFiniteType.isLocallyNoetherian _ _ (T.scheme.obj X).hom
                (T.projective X).isProper.toLocallyOfFiniteType inferInstance)
              ((T.scheme.obj X).hom.relativeDimensionFunction
                (fun _ : Spec (CommRingCat.of k) ↦ 0))
              (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction _ _
                (T.scheme.obj X).hom inferInstance
                (T.projective X).isProper.toLocallyOfFiniteType
                (fun _ : Spec (CommRingCat.of k) ↦ 0) inferInstance) 0
              (CycleGroup.point
                ((T.scheme.obj X).hom.relativeDimensionFunction
                  (fun _ : Spec (CommRingCat.of k) ↦ 0)) 0 x
                (@SchemeOverField.closedPoint_relativeDimensionFunction_eq_zero k _
                  (T.scheme.obj X) (T.projective X).isProper.toLocallyOfFiniteType x))),
      (T.integral hX).toAddMonoidHom.comp
          ((T.cycleClass X).comp
            (CHgrade X (d : ℤ)).subtype.toAddMonoidHom) =
        (Int.castAddHom F).comp
          ((@ChowGroup.degree k _ (T.scheme.obj X) (T.projective X).isProper).comp
            chowTopEquiv.toAddMonoidHom))

end WeilCohomology.SchemeClassicalTheory
