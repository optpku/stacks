/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Degree
public import ReasLib.AlgebraicGeometry.CycleGroup.Point
public import ReasLib.AlgebraicGeometry.Scheme.OverField.ClosedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.GeometricallyIrreducible
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.OverExtension
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.GradedCycleClass

/-!
# Integration and degrees of zero-cycles

This module relates integration of top-degree cycle classes in a scheme-valued classical
Weil cohomology theory to the degree homomorphism on zero-dimensional Chow groups.
-/

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

variable (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
  H CH Hgrade CHgrade cyclePullback cyclePushforward)

/-- Proof-local geometric instance, supplied by the theory rather than assumed
when elaborating relative dimension functions in the statements below. -/
local instance representedSmooth (X : V) : Smooth (T.scheme.obj X).hom := T.smooth X

/-- On a nonempty equidimensional represented scheme, integration of a top-degree cycle
class is the degree of the corresponding zero-cycle class, cast from `ℤ` to `F`. -/
theorem integral_cycleClass_eq_degree
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
    (alpha : CHgrade X (d : ℤ)) :
    T.integral hX (T.cycleClass X alpha) =
      (@ChowGroup.degree k _ (T.scheme.obj X) (T.projective X).isProper
        (chowTopEquiv alpha) : F) := sorry

/-- As additive maps, integration after the top-degree cycle-class map equals the degree
homomorphism followed by the canonical cast from `ℤ` to `F`. -/
theorem integral_comp_cycleClass_eq_degree
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
                (T.scheme.obj X) (T.projective X).isProper.toLocallyOfFiniteType x))) :
    (T.integral hX).toAddMonoidHom.comp
        ((T.cycleClass X).comp
          (CHgrade X (d : ℤ)).subtype.toAddMonoidHom) =
      (Int.castAddHom F).comp
        ((@ChowGroup.degree k _ (T.scheme.obj X) (T.projective X).isProper).comp
          chowTopEquiv.toAddMonoidHom) := sorry


/-- The degree formula with the theory's uniform geometric Chow comparison.
The older formula also allows a separately supplied comparison for interoperability. -/
theorem integral_cycleClass_eq_geometric_degree
    {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (alpha : CHgrade X d) :
    T.integral hX (T.cycleClass X alpha) =
      (@ChowGroup.degree k _ (T.scheme.obj X) (T.projective X).isProper
        (T.chowTopEquiv hX alpha) : F) := by
  exact integral_cycleClass_eq_degree.{u, v, w, x, y, z, 0, 0, 0}
    T hX (T.chowTopEquiv hX)
    (fun x _ ↦ T.closedPointClass_comparison hX x) alpha

/-- The degree formula as an equality of additive maps, using the same uniform
comparison in every occurrence. -/
theorem integral_comp_cycleClass_eq_geometric_degree
    {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) :
    (T.integral hX).toAddMonoidHom.comp
        ((T.cycleClass X).comp (CHgrade X (d : ℤ)).subtype.toAddMonoidHom) =
      (Int.castAddHom F).comp
        ((@ChowGroup.degree k _ (T.scheme.obj X) (T.projective X).isProper).comp
          (T.chowTopEquiv hX).toAddMonoidHom) := by
  exact integral_comp_cycleClass_eq_degree.{u, v, w, x, y, z, 0, 0, 0}
    T hX (T.chowTopEquiv hX)
    (fun x _ ↦ T.closedPointClass_comparison hX x)


/-- For a geometrically irreducible smooth projective scheme over a finite separable
extension `k'/k`, the top-degree cycle-class homomorphism factors through the
integer-valued degree homomorphism on zero cycles. -/
theorem cycleClass_factorsThrough_degree
    {k' : Type u} [Field k'] [Algebra k k'] [Module.Finite k k'] [Algebra.IsSeparable k k']
    {K X : V} (s : X ⟶ K)
    (eK : T.scheme.obj K ≅
      Over.mk (Scheme.AffineBaseChange.specMap k k'))
    {d : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    [GeometricallyIrreducible (T.overExtension s eK).hom]
    [Smooth (T.overExtension s eK).hom]
    [Projective (T.overExtension s eK).hom]
    (chowTopEquiv : CHgrade X (d : ℤ) ≃+
      @ChowGroup (T.overExtension s eK).left
        (LocallyOfFiniteType.isLocallyNoetherian (T.overExtension s eK).hom)
        ((T.overExtension s eK).hom.relativeDimensionFunction
          (fun _ : Spec (CommRingCat.of k') ↦ 0)) inferInstance 0)
    (chowTopEquiv_closedPointClass :
      ∀ x : closedPoints (T.overExtension s eK).left,
        Algebra.IsSeparable k' ((T.overExtension s eK).left.residueField x) →
          chowTopEquiv (T.closedPointClass hX x) =
            @AlgebraicGeometry.chowClass (T.overExtension s eK).left
              (LocallyOfFiniteType.isLocallyNoetherian (T.overExtension s eK).hom)
              ((T.overExtension s eK).hom.relativeDimensionFunction
                (fun _ : Spec (CommRingCat.of k') ↦ 0)) inferInstance 0
              (CycleGroup.point
                ((T.overExtension s eK).hom.relativeDimensionFunction
                  (fun _ : Spec (CommRingCat.of k') ↦ 0)) 0 x
                (SchemeOverField.closedPoint_relativeDimensionFunction_eq_zero
                  (T.overExtension s eK) x))) :
    ∃ factor : ℤ →+ Hgrade X (2 * (d : ℤ)),
      (T.gradedCycleClass X (d : ℤ)).comp
          chowTopEquiv.symm.toAddMonoidHom =
        factor.comp (ChowGroup.degree (T.overExtension s eK)) := sorry

end WeilCohomology.SchemeClassicalTheory
