/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import ReasLib.AlgebraicGeometry.WeilCohomology.Trace
public import ReasLib.AlgebraicGeometry.WeilCohomology.SmoothProjective
public import ReasLib.Topology.KrullDimension.Equidimensional

@[expose] public section

noncomputable section

universe u v w x y z

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators
open scoped TensorProduct

namespace WeilCohomology

/-- An abstract diagonal-cycle interface with chosen cycle-class, diagonal, and
trace data for a graded cohomology theory. -/
structure PreWeilTheory
    (F : Type u) [Field F] [CharZero F]
    (TateLine : Type w) [AddCommGroup TateLine] [Module F TateLine]
    (V : Type v) [Category.{v} V] (H Picard Cycle : V → Type w)
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)] where
  /-- Data (D0): the chosen Tate line is one-dimensional. -/
  tateLine_rank : Module.finrank F TateLine = 1
  /-- The cohomological degree and Tate-twist summands of total cohomology. -/
  Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X)
  /-- The bidegree summands form an exhaustive internal direct-sum decomposition of
  total cohomology. -/
  Hgrade_isInternal : ∀ X, DirectSum.IsInternal (Hgrade X)
  /-- Tensoring with the Tate line raises the twist index by one. -/
  tateTwist : ∀ X i j,
    Hgrade X (i, j) ⊗[F] TateLine ≃ₗ[F] Hgrade X (i, j + 1)
  /-- The unit has bidegree `(0, 0)`. -/
  one_mem : ∀ X, (1 : H X) ∈ Hgrade X (0, 0)
  /-- Cup product adds cohomological degrees and Tate twists. -/
  mul_mem : ∀ X {p q : ℤ × ℤ} (a : Hgrade X p) (b : Hgrade X q),
    (a : H X) * b ∈ Hgrade X (p + q)
  /-- Homogeneous cup products satisfy graded commutativity. -/
  gradedComm : ∀ X {i i' j j' : ℤ} (a : Hgrade X (i, j))
      (b : Hgrade X (i', j')),
    (a : H X) * b = (-1 : H X) ^ (i * i').natAbs * ((b : H X) * a)
  /-- The objects in the smooth-projective domain. -/
  IsSmoothProjective : V → Prop
  /-- Nonempty equidimensional smooth-projective objects of dimension `d`. -/
  IsNonemptyEquidimensional : V → ℕ → Prop
  /-- A nonempty equidimensional object belongs to the smooth-projective domain. -/
  nonemptyEquidimensional_isSmoothProjective : ∀ {X d},
    IsNonemptyEquidimensional X d → IsSmoothProjective X
  /-- The product of two objects. -/
  product : V → V → V
  /-- The first projection from a product. -/
  fst : ∀ X Y, product X Y ⟶ X
  /-- The second projection from a product. -/
  snd : ∀ X Y, product X Y ⟶ Y
  /-- Products add dimensions and preserve nonempty equidimensionality. -/
  product_isNonemptyEquidimensional : ∀ {X Y d e},
    IsNonemptyEquidimensional X d → IsNonemptyEquidimensional Y e →
      IsNonemptyEquidimensional (product X Y) (d + e)
  /-- Data (D1): pullback on total cohomology. -/
  pullback : ∀ {X Y : V}, (X ⟶ Y) → H Y →ₐ[F] H X
  /-- Pullback preserves both the cohomological degree and Tate twist. -/
  pullback_mem : ∀ {X Y : V} (f : X ⟶ Y) (p : ℤ × ℤ)
      (a : Hgrade Y p),
    pullback f a ∈ Hgrade X p
  /-- Pullback by an identity is the identity. -/
  pullback_id : ∀ X, pullback (𝟙 X) = AlgHom.id F (H X)
  /-- Pullback reverses composition. -/
  pullback_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
    pullback (f ≫ g) = (pullback f).comp (pullback g)
  /-- Binary coproducts in the smooth-projective domain. -/
  coproduct : V → V → V
  /-- The left coprojection. -/
  inl : ∀ X Y, X ⟶ coproduct X Y
  /-- The right coprojection. -/
  inr : ∀ X Y, Y ⟶ coproduct X Y
  /-- The assertion that an object is empty. -/
  IsEmpty : V → Prop
  /-- Axiom (A1), empty-object clause: an empty smooth-projective object has zero
  cohomology. -/
  axiomA1_empty : ∀ {X}, IsSmoothProjective X → IsEmpty X → ∀ a : H X, a = 0
  /-- Axiom (A1), coproduct clause: cohomology carries binary coproducts to products. -/
  axiomA1 : ∀ {X Y}, IsSmoothProjective X → IsSmoothProjective Y →
    Function.Bijective (fun a : H (coproduct X Y) ↦
      (pullback (inl X Y) a, pullback (inr X Y) a))
  /-- Pullback of Picard classes. -/
  picardPullback : ∀ {X Y : V}, (X ⟶ Y) → Picard Y →+ Picard X
  /-- Data (D2'): the first Chern class has bidegree `(2, 1)`. -/
  firstChernClass : ∀ X, Picard X →+ Hgrade X (2, 1)
  /-- Axiom (A2): first Chern classes commute with pullback. -/
  axiomA2 : ∀ {X Y : V} (f : X ⟶ Y) (L : Picard Y),
    pullback f (firstChernClass Y L) = firstChernClass X (picardPullback f L)
  /-- The assertion that a morphism is a projective bundle of rank `n`. -/
  IsProjectiveBundle : ∀ {P X : V}, (P ⟶ X) → ℕ → Prop
  /-- The tautological invertible sheaf on a projective bundle. -/
  projectiveBundleLineBundle : ∀ {P X : V} (p : P ⟶ X) (n : ℕ),
    IsProjectiveBundle p n → Picard P
  /-- The graded map occurring in the projective bundle formula. -/
  projectiveBundleMap : ∀ {P X : V} (p : P ⟶ X) (n : ℕ),
    IsProjectiveBundle p n → (i j : ℤ) →
      (∀ r : Fin n, Hgrade X (i - 2 * ((r : ℕ) : ℤ), j - ((r : ℕ) : ℤ))) →ₗ[F]
        Hgrade P (i, j)
  /-- The projective-bundle map is the sum of pullbacks multiplied by powers of the
  first Chern class of the tautological invertible sheaf. -/
  projectiveBundleMap_apply : ∀ {P X : V} (p : P ⟶ X) (n : ℕ)
      (hp : IsProjectiveBundle p n) (i j : ℤ)
      (a : ∀ r : Fin n,
        Hgrade X (i - 2 * ((r : ℕ) : ℤ), j - ((r : ℕ) : ℤ))),
    (projectiveBundleMap p n hp i j a : H P) =
      ∑ r : Fin n, pullback p (a r) *
        (firstChernClass P (projectiveBundleLineBundle p n hp) : H P) ^ (r : ℕ)
  /-- Axiom (A3): the projective bundle map is an isomorphism in every bidegree. -/
  axiomA3 : ∀ {P X : V} (p : P ⟶ X) (n : ℕ)
      (hp : IsProjectiveBundle p n) (i j : ℤ),
    Function.Bijective (projectiveBundleMap p n hp i j)
  /-- The assertion that a morphism includes an effective Cartier divisor. -/
  IsEffectiveCartierDivisor : ∀ {Y X : V}, (Y ⟶ X) → Prop
  /-- The invertible sheaf associated to an effective Cartier divisor. -/
  cartierLineBundle : ∀ {Y X : V} (i : Y ⟶ X),
    IsEffectiveCartierDivisor i → Picard X
  /-- Axiom (A4): a class vanishing on a divisor is annihilated by its class. -/
  axiomA4 : ∀ {Y X : V} (i : Y ⟶ X) (hi : IsEffectiveCartierDivisor i)
      (a : H X),
    pullback i a = 0 → a * firstChernClass X (cartierLineBundle i hi) = 0
  /-- The exterior-product Künneth map. -/
  kunnethMap : ∀ X Y, H X ⊗[F] H Y →ₗ[F] H (product X Y)
  /-- The Künneth map is pullback to the two factors followed by cup product. -/
  kunnethMap_tmul : ∀ {X Y : V} (a : H X) (b : H Y),
    kunnethMap X Y (a ⊗ₜ[F] b) = pullback (fst X Y) a * pullback (snd X Y) b
  /-- The Künneth map adds both grading indices. -/
  kunnethMap_mem : ∀ {X Y : V} {p q : ℤ × ℤ}
      (a : Hgrade X p) (b : Hgrade Y q),
    kunnethMap X Y (a ⊗ₜ[F] b) ∈ Hgrade (product X Y) (p + q)
  /-- The assertion that an object is the spectrum of the base field. -/
  IsBasePoint : V → Prop
  /-- The scalar map from `F` to bidegree `(0, 0)` cohomology of the base point. -/
  pointH0Map : ∀ {X}, IsBasePoint X → F →ₗ[F] Hgrade X (0, 0)
  /-- The scalar map to base-point cohomology agrees with the algebra structure. -/
  pointH0Map_apply : ∀ {X} (hX : IsBasePoint X) (a : F),
    (pointH0Map hX a : H X) = algebraMap F (H X) a
  /-- Axiom (A5), base-point clause: `H⁰(Spec F) = F`. -/
  axiomA5_point : ∀ {X} (hX : IsBasePoint X), Function.Bijective (pointH0Map hX)
  /-- Axiom (A5), Künneth clause: the exterior-product map is an isomorphism on
  smooth-projective objects. -/
  axiomA5 : ∀ {X Y}, IsSmoothProjective X → IsSmoothProjective Y →
    Function.Bijective (kunnethMap X Y)
  /-- The codimension grading on the cycle ring. -/
  cycleGrade : ∀ X, ℤ → Submodule ℤ (Cycle X)
  /-- Cycle products add codimensions. -/
  cycle_mul_mem : ∀ X {i j : ℤ} (a : cycleGrade X i) (b : cycleGrade X j),
    (a : Cycle X) * b ∈ cycleGrade X (i + j)
  /-- Pullback of cycles. -/
  cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → Cycle Y →+* Cycle X
  /-- Cycle pullback preserves codimension. -/
  cyclePullback_mem : ∀ {X Y : V} (f : X ⟶ Y) (i : ℤ)
      (z : cycleGrade Y i),
    cyclePullback f z ∈ cycleGrade X i
  /-- The cycle associated to an effective Cartier divisor. -/
  cartierCycle : ∀ {Y X : V} (i : Y ⟶ X),
    IsEffectiveCartierDivisor i → cycleGrade X 1
  /-- The cycle-class homomorphism canonically induced by the first Chern class
  under (A1)–(A4). -/
  cycleClass : ∀ X, Cycle X →+* H X
  /-- A codimension-`i` cycle has bidegree `(2 * i, i)`. -/
  cycleClass_mem : ∀ X (i : ℤ) (z : cycleGrade X i),
    cycleClass X z ∈ Hgrade X (2 * i, i)
  /-- Cycle classes commute with pullback. -/
  cycleClass_pullback : ∀ {X Y : V} (f : X ⟶ Y) (z : Cycle Y),
    cycleClass X (cyclePullback f z) = pullback f (cycleClass Y z)
  /-- On an effective Cartier divisor, the derived cycle-class map is its first
  Chern class. -/
  cycleClass_cartier : ∀ {Y X : V} (i : Y ⟶ X)
      (hi : IsEffectiveCartierDivisor i),
    cycleClass X (cartierCycle i hi) = firstChernClass X (cartierLineBundle i hi)
  /-- The diagonal cycle of an equidimensional object has codimension its dimension. -/
  diagonalCycle : ∀ {X d}, IsNonemptyEquidimensional X d →
    cycleGrade (product X X) d
  /-- The source-geometric product-diagonal compatibility: after regrouping tensor
  factors, the cycle class of `Δ_(X × Y)` is the exterior product of the cycle
  classes of `Δ_X` and `Δ_Y`. -/
  diagonalCycle_product : ∀ {X Y d e}
      (hX : IsNonemptyEquidimensional X d)
      (hY : IsNonemptyEquidimensional Y e),
    cycleClass (product (product X Y) (product X Y))
        (diagonalCycle (product_isNonemptyEquidimensional hX hY)) =
      kunnethMap (product X Y) (product X Y)
        (TensorProduct.map (kunnethMap X Y) (kunnethMap X Y)
          ((tensorInterchange F (H X) (H Y)).symm
            ((LinearEquiv.ofBijective (kunnethMap X X)
                (axiomA5 (nonemptyEquidimensional_isSmoothProjective hX)
                  (nonemptyEquidimensional_isSmoothProjective hX))).symm
                (cycleClass (product X X) (diagonalCycle hX)) ⊗ₜ[F]
              (LinearEquiv.ofBijective (kunnethMap Y Y)
                (axiomA5 (nonemptyEquidimensional_isSmoothProjective hY)
                  (nonemptyEquidimensional_isSmoothProjective hY))).symm
                (cycleClass (product Y Y) (diagonalCycle hY)))))
  /-- The canonical diagonal tensor is a coevaluation: contraction by it gives
  a perfect identification of linear functionals with cohomology classes. -/
  diagonalTensor_perfect : ∀ {X d} (hX : IsNonemptyEquidimensional X d),
    Function.Bijective (fun trace : H X →ₗ[F] F ↦
      contractRight trace
        ((LinearEquiv.ofBijective (kunnethMap X X)
          (axiomA5 (nonemptyEquidimensional_isSmoothProjective hX)
            (nonemptyEquidimensional_isSmoothProjective hX))).symm
          (cycleClass (product X X) (diagonalCycle hX))))
  /-- The trace on total cohomology, extended by zero from bidegree `(2 * d, d)`. -/
  integral : ∀ {X d}, IsNonemptyEquidimensional X d → H X →ₗ[F] F
  /-- The total trace vanishes outside bidegree `(2 * d, d)`. -/
  integral_vanishes : ∀ {X d} (hX : IsNonemptyEquidimensional X d)
      (p : ℤ × ℤ), p ≠ (2 * (d : ℤ), (d : ℤ)) →
    ∀ a : Hgrade X p, integral hX a = 0
  /-- Axiom (A6): contraction of the diagonal tensor by the trace is the unit. -/
  axiomA6 : ∀ {X d} (hX : IsNonemptyEquidimensional X d),
    contractRight (integral hX)
        ((LinearEquiv.ofBijective (kunnethMap X X)
          (axiomA5 (nonemptyEquidimensional_isSmoothProjective hX)
            (nonemptyEquidimensional_isSmoothProjective hX))).symm
          (cycleClass (product X X) (diagonalCycle hX))) = 1
  /-- The assertion that a morphism is the blowup of a smooth center. -/
  IsBlowupOfSmoothCenter : ∀ {X' X : V}, (X' ⟶ X) → Prop
  /-- Axiom (A7): pullback by the blowup of a smooth center is injective. -/
  axiomA7 : ∀ {X' X : V} (b : X' ⟶ X), IsBlowupOfSmoothCenter b →
    Function.Injective (pullback b)

namespace PreWeilTheory

/-- The canonical Künneth preimage of the cycle class of the diagonal. -/
noncomputable def diagonalTensor
    {F : Type u} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type v} [Category.{v} V] {H Picard Cycle : V → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine V H Picard Cycle) {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d) : H X ⊗[F] H X :=
  (LinearEquiv.ofBijective (T.kunnethMap X X)
    (T.axiomA5 (T.nonemptyEquidimensional_isSmoothProjective hX)
      (T.nonemptyEquidimensional_isSmoothProjective hX))).symm
    (T.cycleClass (T.product X X) (T.diagonalCycle hX))

/-- The canonical diagonal tensor maps to the cycle class of the diagonal. -/
theorem diagonalTensor_spec
    {F : Type u} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type v} [Category.{v} V] {H Picard Cycle : V → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine V H Picard Cycle) {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d) :
    T.kunnethMap X X (T.diagonalTensor hX) =
      T.cycleClass (T.product X X) (T.diagonalCycle hX) := sorry

/-- The diagonal tensor of a product is the regrouped tensor product of the two
factor diagonal tensors. -/
theorem diagonalTensor_product
    {F : Type u} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type v} [Category.{v} V] {H Picard Cycle : V → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine V H Picard Cycle) {X Y : V} {d e : ℕ}
    (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y e) :
    tensorInterchange F (H X) (H Y)
        (TensorProduct.map
          (LinearEquiv.ofBijective (T.kunnethMap X Y)
            (T.axiomA5 (T.nonemptyEquidimensional_isSmoothProjective hX)
              (T.nonemptyEquidimensional_isSmoothProjective hY))).symm.toLinearMap
          (LinearEquiv.ofBijective (T.kunnethMap X Y)
            (T.axiomA5 (T.nonemptyEquidimensional_isSmoothProjective hX)
              (T.nonemptyEquidimensional_isSmoothProjective hY))).symm.toLinearMap
          (T.diagonalTensor (T.product_isNonemptyEquidimensional hX hY))) =
      T.diagonalTensor hX ⊗ₜ[F] T.diagonalTensor hY := sorry

/-- The nondegeneracy consequence of (A6): contraction against the diagonal tensor
characterizes the zero-extended top-degree trace. -/
theorem axiomA6_unique
    {F : Type u} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type v} [Category.{v} V] {H Picard Cycle : V → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine V H Picard Cycle) {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d) (trace : H X →ₗ[F] F) :
    contractRight trace (T.diagonalTensor hX) = 1 → trace = T.integral hX := sorry

/-- Replace the chosen Tate-shift identifications while retaining the same graded
cohomology data and axioms. -/
def withTateTwist
    {F : Type u} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type v} [Category.{v} V] {H Picard Cycle : V → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine V H Picard Cycle)
    (tateTwist : ∀ X i j,
      T.Hgrade X (i, j) ⊗[F] TateLine ≃ₗ[F] T.Hgrade X (i, j + 1)) :
    PreWeilTheory F TateLine V H Picard Cycle :=
  { T with tateTwist := tateTwist }

/-- The restriction of the total trace to the top cohomological degree and matching
Tate twist. -/
noncomputable def topIntegral
    {F : Type u} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type v} [Category.{v} V] {H Picard Cycle : V → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine V H Picard Cycle) {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d) :
    T.Hgrade X (2 * (d : ℤ), (d : ℤ)) →ₗ[F] F :=
  (T.integral hX).comp (T.Hgrade X (2 * (d : ℤ), (d : ℤ))).subtype

end PreWeilTheory

/-- Data (D0), (D1), and (D2') on a presentation of all smooth projective
`k`-schemes, together with axioms (A1)–(A7). -/
structure SchemePreWeilTheory
    (k : Type u) [Field k]
    (F : Type v) [Field F] [CharZero F]
    (TateLine : Type x) [AddCommGroup TateLine] [Module F TateLine]
    (V : Type w) [Category.{z} V]
    (dimension : V → ℕ) (product : V → V → V)
    (fst : ∀ X Y, product X Y ⟶ X) (snd : ∀ X Y, product X Y ⟶ Y)
    (point : V) (CH : V → Type y) [∀ X, CommRing (CH X)]
    (CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)) [∀ X, GradedAlgebra (CHgrade X)]
    (cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X)
    (cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y)
    (pointCycle : CHgrade point 0)
    (H Picard : V → Type x)
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] where
  /-- The functor realizing the abstract domain as schemes over `k`. -/
  scheme : V ⥤ SchemeOverField k
  /-- Morphisms in the presentation are precisely morphisms of the represented schemes. -/
  scheme_fullyFaithful : scheme.FullyFaithful
  /-- Every represented scheme is smooth over `k`. -/
  smooth : ∀ X, Smooth (scheme.obj X).hom
  /-- Every represented scheme is projective over `k`. -/
  projective : ∀ X, Projective (scheme.obj X).hom
  /-- The specified dimension is the geometric Krull dimension. -/
  dimension_eq : ∀ X,
    topologicalKrullDim (scheme.obj X).left = (dimension X : WithBot ℕ∞)
  /-- The specified binary product represents the fibre product over `Spec(k)`. -/
  schemeProduct : ∀ X Y, scheme.obj (product X Y) ≅ scheme.obj X ⨯ scheme.obj Y
  /-- The specified first projection is the geometric product projection. -/
  scheme_fst : ∀ X Y, scheme.map (fst X Y) =
    (schemeProduct X Y).hom ≫ Limits.prod.fst
  /-- The specified second projection is the geometric product projection. -/
  scheme_snd : ∀ X Y, scheme.map (snd X Y) =
    (schemeProduct X Y).hom ≫ Limits.prod.snd
  /-- The specified point represents `Spec(k)` over itself. -/
  schemePoint : scheme.obj point ≅ Over.mk (𝟙 (Spec (CommRingCat.of k)))
  /-- Every smooth projective scheme over `k` is represented by an object of `V`. -/
  scheme_essentiallySurjective : ∀ (S : SchemeOverField k)
    [Smooth S.hom] [Projective S.hom],
    ∃ X : V, Nonempty (scheme.obj X ≅ S)
  /-- Chow pullback by an identity is the identity. -/
  cyclePullback_id : ∀ X,
    cyclePullback (𝟙 X) = GradedAlgHom.id ℤ (CHgrade X)
  /-- Chow pullback reverses composition. -/
  cyclePullback_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
    cyclePullback (f ≫ g) = (cyclePullback f).comp (cyclePullback g)
  /-- Chow pushforward by an identity is the identity. -/
  cyclePushforward_id : ∀ X,
    cyclePushforward (𝟙 X) = AddMonoidHom.id (CH X)
  /-- Chow pushforward preserves composition. -/
  cyclePushforward_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
    cyclePushforward (f ≫ g) = (cyclePushforward g).comp (cyclePushforward f)
  /-- The predicate that a represented scheme is nonempty and equidimensional of
  dimension `d`. -/
  IsNonemptyEquidimensional : V → ℕ → Prop
  /-- The nonempty-equidimensional predicate has its intended geometric meaning. -/
  nonemptyEquidimensional_iff : ∀ {X d}, IsNonemptyEquidimensional X d ↔
    Nonempty (scheme.obj X).left ∧ EquidimensionalSpace (scheme.obj X).left ∧
      dimension X = d
  /-- Products of nonempty equidimensional schemes are nonempty equidimensional,
  with dimensions adding. -/
  product_isNonemptyEquidimensional : ∀ {X Y d e},
    IsNonemptyEquidimensional X d → IsNonemptyEquidimensional Y e →
      IsNonemptyEquidimensional (product X Y) (d + e)
  /-- Data (D0): the chosen Tate line is one-dimensional. -/
  tateLine_rank : Module.finrank F TateLine = 1
  /-- Data (D0): the cohomological-degree and Tate-twist summands. -/
  Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X)
  /-- The bidegree summands exhaust total cohomology as an internal direct sum. -/
  Hgrade_isInternal : ∀ X, DirectSum.IsInternal (Hgrade X)
  /-- Tensoring with the Tate line raises the twist index by one. -/
  tateTwist : ∀ X i j,
    Hgrade X (i, j) ⊗[F] TateLine ≃ₗ[F] Hgrade X (i, j + 1)
  /-- The unit has bidegree `(0, 0)`. -/
  one_mem : ∀ X, (1 : H X) ∈ Hgrade X (0, 0)
  /-- Cup product adds cohomological degrees and Tate twists. -/
  mul_mem : ∀ X {p q : ℤ × ℤ} (a : Hgrade X p) (b : Hgrade X q),
    (a : H X) * b ∈ Hgrade X (p + q)
  /-- Homogeneous cup products satisfy graded commutativity. -/
  gradedComm : ∀ X {i i' j j' : ℤ} (a : Hgrade X (i, j))
      (b : Hgrade X (i', j')),
    (a : H X) * b = (-1 : H X) ^ (i * i').natAbs * ((b : H X) * a)
  /-- Data (D1): pullback on total cohomology. -/
  pullback : ∀ {X Y : V}, (X ⟶ Y) → H Y →ₐ[F] H X
  /-- Pullback preserves cohomological degree and Tate twist. -/
  pullback_mem : ∀ {X Y : V} (f : X ⟶ Y) (p : ℤ × ℤ)
      (a : Hgrade Y p),
    pullback f a ∈ Hgrade X p
  /-- Pullback by an identity is the identity. -/
  pullback_id : ∀ X, pullback (𝟙 X) = AlgHom.id F (H X)
  /-- Pullback reverses composition. -/
  pullback_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
    pullback (f ≫ g) = (pullback f).comp (pullback g)
  /-- A chosen binary disjoint union in the smooth-projective presentation. -/
  coproduct : V → V → V
  /-- The left coprojection. -/
  inl : ∀ X Y, X ⟶ coproduct X Y
  /-- The right coprojection. -/
  inr : ∀ X Y, Y ⟶ coproduct X Y
  /-- The assertion that an object is empty. -/
  IsEmpty : V → Prop
  /-- Axiom (A1), empty clause: an empty object has zero cohomology. -/
  axiomA1_empty : ∀ {X}, IsEmpty X → ∀ a : H X, a = 0
  /-- Axiom (A1), disjoint-union clause: cohomology carries binary disjoint
  unions to products. -/
  axiomA1 : ∀ X Y, Function.Bijective (fun a : H (coproduct X Y) ↦
    (pullback (inl X Y) a, pullback (inr X Y) a))
  /-- Pullback of Picard classes. -/
  picardPullback : ∀ {X Y : V}, (X ⟶ Y) → Picard Y →+ Picard X
  /-- Data (D2'): the first Chern class has bidegree `(2, 1)`. -/
  firstChernClass : ∀ X, Picard X →+ Hgrade X (2, 1)
  /-- Axiom (A2): first Chern classes commute with pullback. -/
  axiomA2 : ∀ {X Y : V} (f : X ⟶ Y) (L : Picard Y),
    pullback f (firstChernClass Y L) = firstChernClass X (picardPullback f L)
  /-- The assertion that a morphism is a projective bundle of rank `n`. -/
  IsProjectiveBundle : ∀ {P X : V}, (P ⟶ X) → ℕ → Prop
  /-- The tautological invertible sheaf on a projective bundle. -/
  projectiveBundleLineBundle : ∀ {P X : V} (p : P ⟶ X) (n : ℕ),
    IsProjectiveBundle p n → Picard P
  /-- The graded map in the projective-bundle formula. -/
  projectiveBundleMap : ∀ {P X : V} (p : P ⟶ X) (n : ℕ),
    IsProjectiveBundle p n → (i j : ℤ) →
      (∀ r : Fin n, Hgrade X (i - 2 * ((r : ℕ) : ℤ), j - ((r : ℕ) : ℤ))) →ₗ[F]
        Hgrade P (i, j)
  /-- The projective-bundle map is the sum of pullbacks multiplied by powers of
  the tautological first Chern class. -/
  projectiveBundleMap_apply : ∀ {P X : V} (p : P ⟶ X) (n : ℕ)
      (hp : IsProjectiveBundle p n) (i j : ℤ)
      (a : ∀ r : Fin n,
        Hgrade X (i - 2 * ((r : ℕ) : ℤ), j - ((r : ℕ) : ℤ))),
    (projectiveBundleMap p n hp i j a : H P) =
      ∑ r : Fin n, pullback p (a r) *
        (firstChernClass P (projectiveBundleLineBundle p n hp) : H P) ^ (r : ℕ)
  /-- Axiom (A3): the projective-bundle map is an isomorphism in every bidegree. -/
  axiomA3 : ∀ {P X : V} (p : P ⟶ X) (n : ℕ)
      (hp : IsProjectiveBundle p n) (i j : ℤ),
    Function.Bijective (projectiveBundleMap p n hp i j)
  /-- The assertion that a morphism includes an effective Cartier divisor. -/
  IsEffectiveCartierDivisor : ∀ {Y X : V}, (Y ⟶ X) → Prop
  /-- The invertible sheaf associated to an effective Cartier divisor. -/
  cartierLineBundle : ∀ {Y X : V} (i : Y ⟶ X),
    IsEffectiveCartierDivisor i → Picard X
  /-- Axiom (A4): a class vanishing on a divisor is annihilated by its class. -/
  axiomA4 : ∀ {Y X : V} (i : Y ⟶ X) (hi : IsEffectiveCartierDivisor i)
      (a : H X),
    pullback i a = 0 → a * firstChernClass X (cartierLineBundle i hi) = 0
  /-- The scalar map to bidegree `(0, 0)` cohomology of the point. -/
  pointH0Map : F →ₗ[F] Hgrade point (0, 0)
  /-- The scalar map to point cohomology agrees with the algebra structure. -/
  pointH0Map_apply : ∀ a : F,
    (pointH0Map a : H point) = algebraMap F (H point) a
  /-- The exterior-product Künneth map. -/
  kunnethMap : ∀ X Y, H X ⊗[F] H Y →ₗ[F] H (product X Y)
  /-- The Künneth map is pullback to the two factors followed by cup product. -/
  kunnethMap_tmul : ∀ {X Y : V} (a : H X) (b : H Y),
    kunnethMap X Y (a ⊗ₜ[F] b) =
      pullback (fst X Y) a * pullback (snd X Y) b
  /-- The Künneth map adds both grading indices. -/
  kunnethMap_mem : ∀ {X Y : V} {p q : ℤ × ℤ}
      (a : Hgrade X p) (b : Hgrade Y q),
    kunnethMap X Y (a ⊗ₜ[F] b) ∈ Hgrade (product X Y) (p + q)
  /-- Axiom (A5), point clause: `H⁰(point) = F`. -/
  axiomA5_point : Function.Bijective pointH0Map
  /-- Axiom (A5), Künneth clause: exterior product is an isomorphism for every
  pair of smooth projective schemes. -/
  axiomA5 : ∀ X Y, Function.Bijective (kunnethMap X Y)
  /-- The cycle-class homomorphism canonically induced by the first Chern class. -/
  cycleClass : ∀ X, CH X →+ H X
  /-- A codimension-`i` cycle has bidegree `(2 * i, i)`. -/
  cycleClass_mem : ∀ X (i : ℤ) (z : CHgrade X i),
    cycleClass X z ∈ Hgrade X (2 * i, i)
  /-- Cycle classes commute with pullback. -/
  cycleClass_pullback : ∀ {X Y : V} (f : X ⟶ Y) (z : CH Y),
    cycleClass X (cyclePullback f z) = pullback f (cycleClass Y z)
  /-- Cycle classes carry intersection products to cup products. -/
  cycleClass_mul : ∀ X (a b : CH X),
    cycleClass X (a * b) = cycleClass X a * cycleClass X b
  /-- The diagonal cycle of a nonempty equidimensional scheme has codimension its
  dimension. -/
  diagonalCycle : ∀ {X d}, IsNonemptyEquidimensional X d →
    CHgrade (product X X) d
  /-- The cycle class of a product diagonal is the exterior product of the two
  factor diagonal classes after regrouping tensor factors. -/
  diagonalCycle_product : ∀ {X Y d e}
      (hX : IsNonemptyEquidimensional X d)
      (hY : IsNonemptyEquidimensional Y e),
    cycleClass (product (product X Y) (product X Y))
        (diagonalCycle (product_isNonemptyEquidimensional hX hY)) =
      kunnethMap (product X Y) (product X Y)
        (TensorProduct.map (kunnethMap X Y) (kunnethMap X Y)
          ((tensorInterchange F (H X) (H Y)).symm
            ((LinearEquiv.ofBijective (kunnethMap X X) (axiomA5 X X)).symm
                (cycleClass (product X X) (diagonalCycle hX)) ⊗ₜ[F]
              (LinearEquiv.ofBijective (kunnethMap Y Y) (axiomA5 Y Y)).symm
                (cycleClass (product Y Y) (diagonalCycle hY)))))
  /-- The trace on total cohomology, extended by zero from bidegree `(2 * d, d)`. -/
  integral : ∀ {X d}, IsNonemptyEquidimensional X d → H X →ₗ[F] F
  /-- The total trace vanishes outside bidegree `(2 * d, d)`. -/
  integral_vanishes : ∀ {X d} (hX : IsNonemptyEquidimensional X d)
      (p : ℤ × ℤ), p ≠ (2 * (d : ℤ), (d : ℤ)) →
    ∀ a : Hgrade X p, integral hX a = 0
  /-- Axiom (A6): contracting the diagonal class by the normalized trace gives the
  cohomological unit. -/
  axiomA6 : ∀ {X d} (hX : IsNonemptyEquidimensional X d),
    contractRight (integral hX)
        ((LinearEquiv.ofBijective (kunnethMap X X) (axiomA5 X X)).symm
          (cycleClass (product X X) (diagonalCycle hX))) = 1
  /-- The assertion that a morphism is the blowup of a smooth center. -/
  IsBlowupOfSmoothCenter : ∀ {X' X : V}, (X' ⟶ X) → Prop
  /-- Axiom (A7): pullback by the blowup of a smooth center is injective. -/
  axiomA7 : ∀ {X' X : V} (b : X' ⟶ X),
    IsBlowupOfSmoothCenter b → Function.Injective (pullback b)

namespace SchemePreWeilTheory

/-- The canonical Künneth preimage of the cycle class of the diagonal. -/
noncomputable def diagonalTensor
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0} {H Picard : V → Type x}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, AddCommGroup (Picard X)]
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
    {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) : H X ⊗[F] H X :=
  (LinearEquiv.ofBijective (T.kunnethMap X X) (T.axiomA5 X X)).symm
    (T.cycleClass (product X X) (T.diagonalCycle hX))

/-- The canonical diagonal tensor maps to the cycle class of the diagonal. -/
theorem diagonalTensor_spec
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0} {H Picard : V → Type x}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, AddCommGroup (Picard X)]
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
    {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) :
    T.kunnethMap X X (T.diagonalTensor hX) =
      T.cycleClass (product X X) (T.diagonalCycle hX) := sorry

/-- The diagonal tensor of a product is the regrouped tensor product of the two
factor diagonal tensors. -/
theorem diagonalTensor_product
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0} {H Picard : V → Type x}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, AddCommGroup (Picard X)]
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
    {X Y : V} {d e : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y e) :
    tensorInterchange F (H X) (H Y)
        (TensorProduct.map
          (LinearEquiv.ofBijective (T.kunnethMap X Y)
            (T.axiomA5 X Y)).symm.toLinearMap
          (LinearEquiv.ofBijective (T.kunnethMap X Y)
            (T.axiomA5 X Y)).symm.toLinearMap
          (T.diagonalTensor (T.product_isNonemptyEquidimensional hX hY))) =
      T.diagonalTensor hX ⊗ₜ[F] T.diagonalTensor hY := sorry

/-- The normalized diagonal equation uniquely characterizes the trace. -/
theorem axiomA6_unique
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0} {H Picard : V → Type x}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, AddCommGroup (Picard X)]
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
    {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (trace : H X →ₗ[F] F) :
    contractRight trace (T.diagonalTensor hX) = 1 → trace = T.integral hX := sorry

/-- Replace the chosen Tate-shift identifications while retaining the same underlying
data and axioms. -/
def withTateTwist
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0} {H Picard : V → Type x}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, AddCommGroup (Picard X)]
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
    (tateTwist : ∀ X i j,
      T.Hgrade X (i, j) ⊗[F] TateLine ≃ₗ[F] T.Hgrade X (i, j + 1)) :
    SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard :=
  { T with tateTwist := tateTwist }

end SchemePreWeilTheory

variable {k : Type u} [Field k]
variable {F : Type v} [Field F] [CharZero F]
variable {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
variable {pointCycle : CHgrade point 0} {H Picard : V → Type x}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, AddCommGroup (Picard X)]

/-- The exterior-product map of a scheme pre-Weil theory is bijective. -/
theorem kunnethMap_bijective_of_axiomsA1ToA7
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
    (X Y : V) :
    Function.Bijective (T.kunnethMap X Y) := sorry

/-- Integration on a product is the tensor-product trace transported across the
Künneth isomorphism. -/
theorem integral_eq_tensorProductTrace_of_axiomsA1ToA7
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
    (X Y : V) {d e : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y e) :
    T.integral (T.product_isNonemptyEquidimensional hX hY) =
      tensorProductTrace (T.kunnethMap X Y)
        (kunnethMap_bijective_of_axiomsA1ToA7 T X Y)
        (T.integral hX) (T.integral hY) := sorry

/-- The integral of an exterior product is the product of the two integrals. -/
theorem integral_kunnethMap_tmul_of_axiomsA1ToA7
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
    (X Y : V) {d e : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y e) (a : H X) (b : H Y) :
    T.integral (T.product_isNonemptyEquidimensional hX hY)
        (T.kunnethMap X Y (a ⊗ₜ[F] b)) =
      T.integral hX a * T.integral hY b := sorry

end WeilCohomology
