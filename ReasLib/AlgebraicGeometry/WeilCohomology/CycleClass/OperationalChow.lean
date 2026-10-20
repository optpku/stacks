/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.CycleClass.ChernCharacter
public import ReasLib.AlgebraicGeometry.ChowCohomology.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.ChernCharacter
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field
public import ReasLib.AlgebraicGeometry.WeilCohomology.SmoothProjective

@[expose] public section

open Algebra.TensorProduct AlgebraicGeometry CategoryTheory
open scoped DirectSum TensorProduct

noncomputable section

universe u v w x y z q

namespace WeilCohomology

namespace OperationalChow

/-- Pullback on canonical nonnegative operational Chow cohomology. -/
def pullback {k : Type u} [Field k] {V : Type w} [Category.{z} V]
    (scheme : V ⥤ SchemeOverField k) {X Y : V} (f : X ⟶ Y)
    [Variety (scheme.obj X)] [Variety (scheme.obj Y)] :
    ChowCohomology.Nonnegative.ring (fun _ ↦ 0) (scheme.obj Y).hom →+*
      ChowCohomology.Nonnegative.ring (fun _ ↦ 0) (scheme.obj X).hom :=
  DirectSum.toSemiring
    (fun n ↦ (DirectSum.of
      (ChowCohomology.Nonnegative.degree (fun _ ↦ 0) (scheme.obj X).hom) n).comp
        (ChowCohomology.restrictDegree (fun _ ↦ 0) (scheme.map f) (n : ℤ)))
    (by
      change DirectSum.of _ 0 _ = DirectSum.of _ 0 _
      congr 1)
    (by
      intro i j a b
      change DirectSum.of _ (i + j) _ = DirectSum.of _ i _ * DirectSum.of _ j _
      rw [DirectSum.of_mul_of]
      congr 1)

/-- Operational Chow pullback along an identity is the identity. -/
theorem pullback_id {k : Type u} [Field k] {V : Type w} [Category.{z} V]
    (scheme : V ⥤ SchemeOverField k) (X : V) [Variety (scheme.obj X)] :
    pullback scheme (𝟙 X) = RingHom.id _ := sorry

/-- Operational Chow pullback reverses composition. -/
theorem pullback_comp {k : Type u} [Field k] {V : Type w} [Category.{z} V]
    (scheme : V ⥤ SchemeOverField k) {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Variety (scheme.obj X)] [Variety (scheme.obj Y)] [Variety (scheme.obj Z)] :
    pullback scheme (f ≫ g) = (pullback scheme f).comp (pullback scheme g) := sorry

end OperationalChow

/-- A pullback-natural graded cycle-class rule on canonical nonnegative operational
Chow cohomology. -/
structure OperationalChowCycleClass
    {k : Type u} [Field k] {V : Type w} [Category.{z} V]
    (scheme : V ⥤ SchemeOverField k) (H : Vᵒᵖ ⥤ RingCat.{q})
    (Hdiag : ∀ X, ℕ → Submodule ℤ (H.obj (Opposite.op X)))
    [∀ X, Variety (scheme.obj X)] where
  /-- The graded cycle-class homomorphism on a represented variety. -/
  app : ∀ X, (fun i : ℕ ↦ LinearMap.range (DirectSum.lof ℤ ℕ
    (ChowCohomology.Nonnegative.degree (fun _ ↦ 0) (scheme.obj X).hom) i)) →+*ᵍ Hdiag X
  /-- Cycle classes commute with canonical operational Chow pullback. -/
  naturality : ∀ {X Y : V} (f : X ⟶ Y)
      (a : ChowCohomology.Nonnegative.ring (fun _ ↦ 0) (scheme.obj Y).hom),
    app X (OperationalChow.pullback scheme f a) = H.map f.op (app Y a)

namespace OperationalChowCycleClass

/-- Construct an operational-Chow cycle-class rule from its objectwise maps and
pullback law. -/
def ofLaws
    {k : Type u} [Field k] {V : Type w} [Category.{z} V]
    {scheme : V ⥤ SchemeOverField k} {H : Vᵒᵖ ⥤ RingCat.{q}}
    {Hdiag : ∀ X, ℕ → Submodule ℤ (H.obj (Opposite.op X))}
    [∀ X, Variety (scheme.obj X)]
    (app : ∀ X, (fun i : ℕ ↦ LinearMap.range (DirectSum.lof ℤ ℕ
      (ChowCohomology.Nonnegative.degree (fun _ ↦ 0) (scheme.obj X).hom) i)) →+*ᵍ Hdiag X)
    (naturality : ∀ {X Y : V} (f : X ⟶ Y)
      (a : ChowCohomology.Nonnegative.ring (fun _ ↦ 0) (scheme.obj Y).hom),
      app X (OperationalChow.pullback scheme f a) = H.map f.op (app Y a)) :
    OperationalChowCycleClass scheme H Hdiag where
  app := app
  naturality := naturality

/-- Two operational-Chow cycle-class rules are equal when their objectwise maps agree. -/
theorem ext
    {k : Type u} [Field k] {V : Type w} [Category.{z} V]
    {scheme : V ⥤ SchemeOverField k} {H : Vᵒᵖ ⥤ RingCat.{q}}
    {Hdiag : ∀ X, ℕ → Submodule ℤ (H.obj (Opposite.op X))}
    [∀ X, Variety (scheme.obj X)]
    (gamma gamma' : OperationalChowCycleClass scheme H Hdiag)
    (h : ∀ X, gamma.app X = gamma'.app X) : gamma = gamma' := sorry

/-- The rational extension of one homogeneous coefficient of an operational-Chow
cycle-class rule. -/
def rationalComponent
    {k : Type u} [Field k] {V : Type w} [Category.{z} V]
    {scheme : V ⥤ SchemeOverField k} {H : Vᵒᵖ ⥤ RingCat.{q}}
    {Hdiag : ∀ X, ℕ → Submodule ℤ (H.obj (Opposite.op X))}
    [∀ X, Variety (scheme.obj X)] [∀ X, Algebra ℚ (H.obj (Opposite.op X))]
    (gamma : OperationalChowCycleClass scheme H Hdiag) (X : V) (i : ℕ) :
    ChowCohomology.Nonnegative.RationalDegree (fun _ ↦ 0) (scheme.obj X).hom i →ₗ[ℤ]
      H.obj (Opposite.op X) :=
  TensorProduct.lift
    (LinearMap.mk₂ ℤ
      (fun a r ↦ r • gamma.app X (DirectSum.of
        (ChowCohomology.Nonnegative.degree (fun _ ↦ 0) (scheme.obj X).hom) i a))
      (by intros; simp [smul_add])
      (by intros; simp)
      (by intros; simp [add_smul])
      (by
        intro c a r
        exact smul_assoc c r _))

/-- The rational coefficient map sends `a ⊗ q` to `q • gamma.app X a`. -/
theorem rationalComponent_tmul
    {k : Type u} [Field k] {V : Type w} [Category.{z} V]
    {scheme : V ⥤ SchemeOverField k} {H : Vᵒᵖ ⥤ RingCat.{q}}
    {Hdiag : ∀ X, ℕ → Submodule ℤ (H.obj (Opposite.op X))}
    [∀ X, Variety (scheme.obj X)] [∀ X, Algebra ℚ (H.obj (Opposite.op X))]
    (gamma : OperationalChowCycleClass scheme H Hdiag) (X : V) (i : ℕ)
    (a : ChowCohomology.Nonnegative.degree (fun _ ↦ 0) (scheme.obj X).hom i)
    (r : ℚ) :
    gamma.rationalComponent X i (a ⊗ₜ[ℤ] r) =
      r • gamma.app X (DirectSum.of
        (ChowCohomology.Nonnegative.degree (fun _ ↦ 0) (scheme.obj X).hom) i a) := sorry

/-- A cycle-class rule factors the canonical operational-Chow Chern character
coefficientwise through a cohomological Chern character. -/
def FactorsChernCharacter
    {k : Type u} [Field k] {V : Type w} [Category.{z} V]
    {scheme : V ⥤ SchemeOverField k} {H : Vᵒᵖ ⥤ RingCat.{q}}
    {Hdiag : ∀ X, ℕ → Submodule ℤ (H.obj (Opposite.op X))}
    [∀ X, Variety (scheme.obj X)] [∀ X, Algebra ℚ (H.obj (Opposite.op X))]
    (gamma : OperationalChowCycleClass scheme H Hdiag)
    (chowTheory : ∀ X, AlgebraicGeometry.ChernClass.Theory
      (fun _ : Spec (CommRingCat.of k) ↦ 0) (scheme.obj X).hom)
    (chH : ∀ X, Scheme.VectorBundleK0 (scheme.obj X).left →+*
      PowerSeries (H.obj (Opposite.op X))) : Prop :=
  ∀ X alpha i,
    gamma.rationalComponent X i
        (Scheme.VectorBundleK0.chernCharacter (fun _ ↦ 0) (scheme.obj X).hom
          (chowTheory X) alpha i) =
      PowerSeries.coeff i (chH X alpha)

end OperationalChowCycleClass

/-- Geometric and cohomological Weil data determine a unique pullback-natural graded
cycle-class rule on canonical operational Chow cohomology, characterized by the Chern
character. -/
theorem existsUniqueCycleClass
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    (scheme : V ⥤ SchemeOverField k) [∀ X, Variety (scheme.obj X)]
    [∀ X, Smooth (scheme.obj X).hom] [∀ X, Projective (scheme.obj X).hom]
    (dimension : V → ℕ) (product : V → V → V)
    (fst : ∀ X Y, product X Y ⟶ X) (snd : ∀ X Y, product X Y ⟶ Y)
    (point : V) (scheme_fullyFaithful : scheme.FullyFaithful)
    (dimension_eq : ∀ X,
      topologicalKrullDim (scheme.obj X).left = (dimension X : WithBot ℕ∞))
    (schemeProduct : ∀ X Y, scheme.obj (product X Y) ≅ scheme.obj X ⨯ scheme.obj Y)
    (scheme_fst : ∀ X Y, scheme.map (fst X Y) =
      (schemeProduct X Y).hom ≫ Limits.prod.fst)
    (scheme_snd : ∀ X Y, scheme.map (snd X Y) =
      (schemeProduct X Y).hom ≫ Limits.prod.snd)
    (schemePoint : scheme.obj point ≅ Over.mk (𝟙 (Spec (CommRingCat.of k))))
    (scheme_essentiallySurjective : ∀ (S : SchemeOverField k)
      [Variety S] [Smooth S.hom] [Projective S.hom],
      ∃ X : V, Nonempty (scheme.obj X ≅ S))
    (H : Vᵒᵖ ⥤ RingCat.{q})
    (Hdiag : ∀ X, ℕ → Submodule ℤ (H.obj (Opposite.op X)))
    [∀ X, GradedAlgebra (Hdiag X)] [∀ X, Algebra ℚ (H.obj (Opposite.op X))]
    [∀ X, Algebra F (H.obj (Opposite.op X))]
    (Hgrade : ∀ X, ℤ × ℤ → Submodule F (H.obj (Opposite.op X)))
    (h_diagonal : ∀ X i (a : H.obj (Opposite.op X)),
      a ∈ Hdiag X i ↔ a ∈ Hgrade X (2 * (i : ℤ), (i : ℤ)))
    (tateLine_rank : Module.finrank F TateLine = 1)
    (tateTwist : ∀ X i j,
      Hgrade X (i, j) ⊗[F] TateLine ≃ₗ[F] Hgrade X (i, j + 1))
    (h_pullback_bigrade : ∀ {X Y : V} (f : X ⟶ Y) (p : ℤ × ℤ)
      (a : Hgrade Y p), H.map f.op a ∈ Hgrade X p)
    (chH : ∀ X, Scheme.VectorBundleK0 (scheme.obj X).left →+*
      PowerSeries (H.obj (Opposite.op X)))
    (chH_coeff_mem : ∀ X (alpha : Scheme.VectorBundleK0
      (scheme.obj X).left) i, PowerSeries.coeff i (chH X alpha) ∈ Hdiag X i)
    (chH_naturality : ∀ {X Y : V} (f : X ⟶ Y)
      (alpha : Scheme.VectorBundleK0 (scheme.obj Y).left),
      PowerSeries.map (H.map f.op).hom (chH Y alpha) =
        chH X (Scheme.VectorBundleK0.pullback (scheme.map f).left alpha))
    (chowTheory : ∀ X, AlgebraicGeometry.ChernClass.Theory
      (fun _ : Spec (CommRingCat.of k) ↦ 0) (scheme.obj X).hom) :
    ∃ gamma : OperationalChowCycleClass scheme H Hdiag,
      gamma.FactorsChernCharacter chowTheory chH ∧
        ∀ gamma' : OperationalChowCycleClass scheme H Hdiag,
          gamma'.FactorsChernCharacter chowTheory chH → gamma' = gamma := sorry

end WeilCohomology
