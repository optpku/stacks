/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil
public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.Point
public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.PoincareDuality
public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.SchemePushforward
public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.CycleClassPushforward
public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.SchemeAxiomA8
public import ReasLib.AlgebraicGeometry.WeilCohomology.GradedPullback
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.IsWeil

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct

universe u v w x y z

namespace WeilCohomology.SchemePreWeilTheory

variable {k : Type u} [Field k]
variable {F : Type v} [Field F] [CharZero F]
variable {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
variable {pointCycle : CHgrade point 0} {H Picard : V → Type w}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, AddCommGroup (Picard X)]

variable (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
  cyclePullback cyclePushforward pointCycle H Picard)

/-- The homogeneous pieces of a presented pre-Weil theory are multiplicatively graded. -/
def gradedMonoidHgrade (X : V) : SetLike.GradedMonoid (T.Hgrade X) where
  one_mem := T.one_mem X
  mul_mem := fun {_i _j a b} ha hb ↦ T.mul_mem X ⟨a, ha⟩ ⟨b, hb⟩

/-- The exhaustive homogeneous decomposition of a presented pre-Weil theory gives its
canonical graded-algebra structure. -/
noncomputable def gradedAlgebraHgrade (X : V) : GradedAlgebra (T.Hgrade X) :=
  @DirectSum.IsInternal.gradedAlgebra F _ (H X) _ _ (ℤ) _ _
    (T.Hgrade X) (T.gradedMonoidHgrade X) (T.Hgrade_isInternal X)

/-- The pullback of a presented pre-Weil theory as a bundled graded algebra homomorphism. -/
def gradedPullback {X Y : V} (f : X ⟶ Y) :
    @GradedAlgHom F (H Y) (H X) (ℤ) _ _ _ _ _ _ _
      (T.Hgrade Y) (T.Hgrade X) (T.gradedAlgebraHgrade Y) (T.gradedAlgebraHgrade X) :=
  @GradedAlgHom.mk F (H Y) (H X) (ℤ) _ _ _ _ _ _ _
    (T.Hgrade Y) (T.Hgrade X) (T.gradedAlgebraHgrade Y) (T.gradedAlgebraHgrade X)
    (T.pullback f) (fun {i a} ha ↦ T.pullback_mem f i ⟨a, ha⟩)

/-- The bundled graded pullback agrees with the original pullback on total cohomology. -/
theorem gradedPullback_apply {X Y : V} (f : X ⟶ Y) (a : H Y) :
    T.gradedPullback f a = T.pullback f a := sorry

/-- The morphism to the chosen point object obtained from the geometric structure map. -/
noncomputable def structureMorphism (X : V) : X ⟶ point :=
  T.scheme_fullyFaithful.preimage
    (Over.homMk (T.scheme.obj X).hom ≫ T.schemePoint.inv)

/-- The represented structure morphism is the canonical map to `Spec(k)`. -/
theorem scheme_structureMorphism (X : V) :
    T.scheme.map (T.structureMorphism X) ≫ T.schemePoint.hom =
      Over.homMk (T.scheme.obj X).hom := sorry

/-- The Künneth map is the product of the two bundled graded pullbacks. -/
theorem kunnethMap_tmul_gradedPullback (X Y : V) (a : H X) (b : H Y) :
    T.kunnethMap X Y (a ⊗ₜ[F] b) =
      T.gradedPullback (fst X Y) a * T.gradedPullback (snd X Y) b := sorry

/-- The underlying Chow class chosen among the pushforwards of fundamental classes of
presentations of a closed point. -/
noncomputable def closedPointClassValue {X : V}
    (p : closedPoints (T.scheme.obj X).left) : CH X :=
  Classical.epsilon fun c : CH X ↦
    ∃ (P : V)
      (e : T.scheme.obj P ≅
        Over.mk ((T.scheme.obj X).left.fromSpecResidueField p ≫ (T.scheme.obj X).hom))
      (f : P ⟶ X),
      (T.scheme.map f).left =
          e.hom.left ≫ (T.scheme.obj X).left.fromSpecResidueField p ∧
        c = cyclePushforward f
          (cyclePullback (T.structureMorphism P) (1 : CHgrade point 0))

/-- The chosen closed-point cycle has codimension equal to the dimension of its ambient
nonempty equidimensional scheme. -/
theorem closedPointClassValue_mem {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d)
    (p : closedPoints (T.scheme.obj X).left) :
    T.closedPointClassValue p ∈ CHgrade X d := sorry

/-- The Chow class of a closed point, constructed from a chosen presented copy of its
residue-field spectrum and Chow pushforward. -/
noncomputable def closedPointClass {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d)
    (p : closedPoints (T.scheme.obj X).left) : CHgrade X d :=
  ⟨T.closedPointClassValue p, T.closedPointClassValue_mem hX p⟩

/-- A closed-point class is represented by the pushforward of the fundamental class on a
presentation of its residue-field spectrum. -/
theorem closedPointClass_spec {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d)
    (p : closedPoints (T.scheme.obj X).left) :
    ∃ (P : V)
      (e : T.scheme.obj P ≅
        Over.mk ((T.scheme.obj X).left.fromSpecResidueField p ≫ (T.scheme.obj X).hom))
      (f : P ⟶ X),
      (T.scheme.map f).left =
          e.hom.left ≫ (T.scheme.obj X).left.fromSpecResidueField p ∧
        (T.closedPointClass hX p : CH X) =
          cyclePushforward f
            (cyclePullback (T.structureMorphism P) (1 : CHgrade point 0)) := sorry

/-- Pushing a constructed closed-point class to the point gives its residue-field degree. -/
theorem closedPointClass_pushforward {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d)
    (p : closedPoints (T.scheme.obj X).left)
    [FiniteDimensional k ((T.scheme.obj X).left.residueField p)] :
    cyclePushforward (T.structureMorphism X) (T.closedPointClass hX p) =
      (Module.finrank k ((T.scheme.obj X).left.residueField p) : ℤ) •
        (1 : CHgrade point 0) := sorry

/-- The specified dimension agrees with geometric Krull dimension on nonempty schemes. -/
theorem dimension_eq_of_axiomsA1ToA7 (X : V)
    (hX : Nonempty (T.scheme.obj X).left) :
    topologicalKrullDim (T.scheme.obj X).left = (dimension X : WithBot ℕ∞) :=
  T.dimension_eq X hX

/-- Pullback from the point carries its fundamental class to the unit class. -/
theorem fundamentalClass_pullback_of_axiomsA1ToA7 (X : V) :
    cyclePullback (T.structureMorphism X) (1 : CHgrade point 0) = 1 := sorry

/-- Bundled graded pullback by an identity morphism is the identity. -/
theorem gradedPullback_id (X : V) :
    T.gradedPullback (𝟙 X) = @GradedAlgHom.id F (H X) (ℤ) _ _ _ _ _
      (T.Hgrade X) (T.gradedAlgebraHgrade X) := sorry

/-- Bundled graded pullback reverses composition of morphisms. -/
theorem gradedPullback_comp {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) :
    T.gradedPullback (f ≫ g) = @GradedAlgHom.comp F (H Z) (H Y) (H X) (ℤ) _ _ _ _ _ _ _ _ _
      (T.Hgrade Z) (T.Hgrade Y) (T.Hgrade X)
      (T.gradedAlgebraHgrade Z) (T.gradedAlgebraHgrade Y) (T.gradedAlgebraHgrade X)
      (T.gradedPullback f) (T.gradedPullback g) := sorry

/-- Cohomological pushforward shifts both indices by the dimension difference. -/
theorem pushforward_mem_of_axiomsA1ToA7 {X Y : V} {d e : ℕ}
    (hX : T.IsNonemptyEquidimensional X d) (hY : T.IsNonemptyEquidimensional Y e)
    (f : X ⟶ Y) (i j : ℤ) (a : T.Hgrade X (i)) :
    T.pushforward hX hY f a ∈
      T.Hgrade Y (i + 2 * ((e : ℤ) - d)) := sorry

/-- Cohomological pushforward is adjoint to bundled graded pullback under the trace. -/
theorem pushforward_spec_gradedPullback [T.HasDiagonalClassRelation]  {X Y : V} {d e : ℕ}
    (hX : T.IsNonemptyEquidimensional X d) (hY : T.IsNonemptyEquidimensional Y e)
    (f : X ⟶ Y) (a : H X) (b : H Y) :
    T.integral hX (T.gradedPullback f b * a) =
      T.integral hY (b * T.pushforward hX hY f a) := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

/-- Chow pushforward shifts codimension by the dimension difference. -/
theorem cyclePushforward_mem_of_axiomsA1ToA7 {X Y : V} {d e : ℕ}
    (hX : T.IsNonemptyEquidimensional X d) (hY : T.IsNonemptyEquidimensional Y e)
    (f : X ⟶ Y) (i : ℤ) (alpha : CHgrade X i) :
    cyclePushforward f alpha ∈ CHgrade Y (i + ((e : ℤ) - d)) := sorry

/-- Exterior product is bijective on every pair of external twists. -/
theorem kunnethMap_fixedTwists_of_axiomsA1ToA7 (X Y : V) (r s : ℤ) :
    Function.Bijective (Tate.tensorMap T.tateLine_rank (T.kunnethMap X Y) r s) := sorry

/-- A scheme pre-Weil theory with the explicit diagonal-class mixin and (A8)
determines a classical theory. Geometric anchoring is tracked by RL-2194. -/
noncomputable def toSchemeClassicalTheory [T.HasDiagonalClassRelation]
    (hA8 : T.SatisfiesAxiomA8)  :
    @SchemeClassicalTheory k _ F _ _ TateLine _ _ V _ dimension product fst snd point
      H CH _ _ _ T.Hgrade CHgrade T.gradedAlgebraHgrade inferInstance
      cyclePullback cyclePushforward :=
  @SchemeClassicalTheory.mk k _ F _ _ TateLine _ _ V _ dimension product fst snd point
    H CH _ _ _ T.Hgrade CHgrade T.gradedAlgebraHgrade inferInstance
    cyclePullback cyclePushforward
    (scheme := T.scheme)
    (scheme_fullyFaithful := T.scheme_fullyFaithful)
    (smooth := T.smooth)
    (projective := T.projective)
    (dimension_eq := T.dimension_eq_of_axiomsA1ToA7)
    (schemeProduct := T.schemeProduct)
    (scheme_fst := T.scheme_fst)
    (scheme_snd := T.scheme_snd)
    (schemePoint := T.schemePoint)
    (structureMorphism := T.structureMorphism)
    (scheme_structureMorphism := T.scheme_structureMorphism)
    (scheme_essentiallySurjective := T.scheme_essentiallySurjective)
    (cyclePullback_id := T.cyclePullback_id)
    (cyclePullback_comp := T.cyclePullback_comp)
    (cyclePushforward_id := T.cyclePushforward_id)
    (cyclePushforward_comp := T.cyclePushforward_comp)
    (IsNonemptyEquidimensional := T.IsNonemptyEquidimensional)
    (nonemptyEquidimensional_iff := T.nonemptyEquidimensional_iff)
    (product_isNonemptyEquidimensional := T.product_isNonemptyEquidimensional)
    (point_isNonemptyEquidimensional := T.point_isNonemptyEquidimensional)
    (fundamentalClass_pullback := T.fundamentalClass_pullback_of_axiomsA1ToA7)
    (closedPointClass := T.closedPointClass)
    (closedPointClass_pushforward := T.closedPointClass_pushforward)
    (tateLine_rank := T.tateLine_rank)
    (Hgrade_isInternal := T.Hgrade_isInternal)
    (pullback := T.gradedPullback)
    (pullback_id := T.gradedPullback_id)
    (pullback_comp := T.gradedPullback_comp)
    (gradedComm := T.gradedComm)
    (cycleClass := T.cycleClass)
    (cycleClass_mem := T.cycleClass_mem)
    (integral := T.integral)
    (integral_vanishes := T.integral_vanishes)
    (finiteDimensional := T.finiteDimensional_of_axiomsA1ToA7)
    (poincarePairing := T.poincarePairing)
    (poincarePairing_apply := T.poincarePairing_apply)
    (poincarePairing_bijective := T.poincarePairing_bijective_of_axiomsA1ToA7)
    (pushforward := T.pushforward)
    (pushforward_mem := T.pushforward_mem_of_axiomsA1ToA7)
    (pushforward_spec := T.pushforward_spec_gradedPullback)
    (kunnethMap := T.kunnethMap)
    (kunnethMap_tmul := T.kunnethMap_tmul_gradedPullback)
    (kunnethMap_mem := fun _X _Y _p _q a b ↦ T.kunnethMap_mem a b)
    (kunnethMap_fixedTwists := T.kunnethMap_fixedTwists_of_axiomsA1ToA7)
    (integral_kunnethMap_tmul := fun {X Y : V} {d e : ℕ} hX hY a b ↦
      integral_kunnethMap_tmul_of_axiomsA1ToA7 T X Y hX hY a b)
    (cyclePushforward_mem := T.cyclePushforward_mem_of_axiomsA1ToA7)
    (cycleClass_pullback := fun f beta ↦ T.cycleClass_pullback f beta)
    (cycleClass_pushforward := cycleClass_pushforward_of_axiomsA1ToA8 T hA8)
    (cycleClass_mul := T.cycleClass_mul)
    (point_normalization := T.point_normalization)

/-- The conversion retains the geometric realization functor. -/
theorem toSchemeClassicalTheory_scheme [T.HasDiagonalClassRelation] (hA8 : T.SatisfiesAxiomA8)  :
  (@SchemeClassicalTheory.scheme k _ F _ _ TateLine _ _ V _ dimension product fst snd point
    H CH _ _ _ T.Hgrade CHgrade T.gradedAlgebraHgrade inferInstance
    cyclePullback cyclePushforward (T.toSchemeClassicalTheory hA8)) = T.scheme := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

/-- The conversion retains the cycle-class homomorphism. -/
theorem toSchemeClassicalTheory_cycleClass [T.HasDiagonalClassRelation] (hA8 : T.SatisfiesAxiomA8)  (X : V) :
  (@SchemeClassicalTheory.cycleClass k _ F _ _ TateLine _ _ V _ dimension product fst snd point
    H CH _ _ _ T.Hgrade CHgrade T.gradedAlgebraHgrade inferInstance
    cyclePullback cyclePushforward (T.toSchemeClassicalTheory hA8)) X = T.cycleClass X := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

/-- The conversion retains the geometric nonempty-equidimensional predicate. -/
theorem toSchemeClassicalTheory_isNonemptyEquidimensional [T.HasDiagonalClassRelation]
    (hA8 : T.SatisfiesAxiomA8)  {X : V} {d : ℕ} :
  (@SchemeClassicalTheory.IsNonemptyEquidimensional k _ F _ _ TateLine _ _ V _ dimension product fst snd point
    H CH _ _ _ T.Hgrade CHgrade T.gradedAlgebraHgrade inferInstance
    cyclePullback cyclePushforward (T.toSchemeClassicalTheory hA8)) X d ↔
      T.IsNonemptyEquidimensional X d := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

/-- The conversion retains the zero-extended trace. -/
theorem toSchemeClassicalTheory_integral [T.HasDiagonalClassRelation] (hA8 : T.SatisfiesAxiomA8) 
    {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) :
  (@SchemeClassicalTheory.integral k _ F _ _ TateLine _ _ V _ dimension product fst snd point
    H CH _ _ _ T.Hgrade CHgrade T.gradedAlgebraHgrade inferInstance
    cyclePullback cyclePushforward (T.toSchemeClassicalTheory hA8))
        ((T.toSchemeClassicalTheory_isNonemptyEquidimensional hA8).mpr hX) =
      T.integral hX := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

/-- The conversion retains the Poincaré-duality pushforward. -/
theorem toSchemeClassicalTheory_pushforward [T.HasDiagonalClassRelation] (hA8 : T.SatisfiesAxiomA8) 
    {X Y : V} {d e : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y e) (f : X ⟶ Y) :
  (@SchemeClassicalTheory.pushforward k _ F _ _ TateLine _ _ V _ dimension product fst snd point
    H CH _ _ _ T.Hgrade CHgrade T.gradedAlgebraHgrade inferInstance
    cyclePullback cyclePushforward (T.toSchemeClassicalTheory hA8))
        ((T.toSchemeClassicalTheory_isNonemptyEquidimensional hA8).mpr hX)
        ((T.toSchemeClassicalTheory_isNonemptyEquidimensional hA8).mpr hY) f =
      T.pushforward hX hY f := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

/-- The conversion retains the Künneth map. -/
theorem toSchemeClassicalTheory_kunnethMap [T.HasDiagonalClassRelation] (hA8 : T.SatisfiesAxiomA8)  (X Y : V) :
  (@SchemeClassicalTheory.kunnethMap k _ F _ _ TateLine _ _ V _ dimension product fst snd point
    H CH _ _ _ T.Hgrade CHgrade T.gradedAlgebraHgrade inferInstance
    cyclePullback cyclePushforward (T.toSchemeClassicalTheory hA8)) X Y = T.kunnethMap X Y := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

/-- Degree-zero pullback in the converted theory is the original restricted pullback. -/
theorem toSchemeClassicalTheory_degreeZeroPullback [T.HasDiagonalClassRelation] (hA8 : T.SatisfiesAxiomA8) 
    {X Y : V} (f : X ⟶ Y) (a : T.Hgrade Y (0)) :
  (@SchemeClassicalTheory.degreeZeroPullback k _ F _ _ TateLine _ _ V _ dimension product fst snd point
    H CH _ _ _ T.Hgrade CHgrade T.gradedAlgebraHgrade inferInstance
    cyclePullback cyclePushforward (T.toSchemeClassicalTheory hA8)) f a =
      T.pullbackGrade f 0 a := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

/-- A scheme pre-Weil theory with the explicit diagonal-class mixin and (A8)
is a Weil theory. Geometric anchoring is tracked by RL-2194. -/
theorem isWeil_of_axiomsA1ToA8 [T.HasDiagonalClassRelation] (hA8 : T.SatisfiesAxiomA8)  :
  (@SchemeClassicalTheory.IsWeil k _ F _ _ TateLine _ _ V _ dimension product fst snd point
    H CH _ _ _ T.Hgrade CHgrade T.gradedAlgebraHgrade inferInstance
    cyclePullback cyclePushforward (T.toSchemeClassicalTheory hA8)) := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

end WeilCohomology.SchemePreWeilTheory
