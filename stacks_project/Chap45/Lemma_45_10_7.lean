/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.Degree
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w x y z

/- Lemma 45.10.7: given a scheme-valued classical Weil cohomology theory satisfying
(A), (B), and (C), a finite separable extension `k'/k`, and a geometrically irreducible
smooth projective `k'`-scheme `X` of dimension `d`, the top-degree cycle-class map
`γ : CH_0(X) → H^{2d}(X)(d)` factors through `deg : CH_0(X) → ℤ`. -/
@[stacks 0FHV] #check (WeilCohomology.SchemeClassicalTheory.cycleClass_factorsThrough_degree :
  ∀ {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {H : V → Type x} {CH : V → Type y}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
    {Hgrade : ∀ X, ℤ → Submodule F (H X)}
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
    [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    (T : WeilCohomology.SchemeClassicalTheory k F TateLine V dimension product fst snd
      point H CH Hgrade CHgrade cyclePullback cyclePushforward)
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
                  (T.overExtension s eK) x))),
    ∃ factor : ℤ →+ Hgrade X (2 * (d : ℤ)),
      (T.gradedCycleClass X (d : ℤ)).comp
          chowTopEquiv.symm.toAddMonoidHom =
        factor.comp (ChowGroup.degree (T.overExtension s eK)))
