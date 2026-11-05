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
  /-- The single cohomological-degree summands of total cohomology. -/
  Hgrade : ∀ X, ℤ → Submodule F (H X)
  /-- The cohomological-degree summands form an exhaustive internal direct-sum decomposition of
  total cohomology. -/
  Hgrade_isInternal : ∀ X, DirectSum.IsInternal (Hgrade X)
  /-- The unit has cohomological degree zero. -/
  one_mem : ∀ X, (1 : H X) ∈ Hgrade X (0)
  /-- Cup product adds cohomological degrees; external twists are handled by Tate.tensorMap. -/
  mul_mem : ∀ X {p q : ℤ} (a : Hgrade X p) (b : Hgrade X q),
    (a : H X) * b ∈ Hgrade X (p + q)
  /-- Homogeneous cup products satisfy graded commutativity. -/
  gradedComm : ∀ X {i i' : ℤ} (a : Hgrade X (i))
      (b : Hgrade X (i')),
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
  /-- Pullback preserves the cohomological degree. -/
  pullback_mem : ∀ {X Y : V} (f : X ⟶ Y) (p : ℤ)
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
  /-- Data (D2'): the first Chern class has bidegree `2`. -/
  firstChernClass : ∀ X, Picard X →+ Hgrade X (2)
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
      (∀ r : Fin n, Hgrade X (i - 2 * ((r : ℕ) : ℤ))) →ₗ[F]
        Hgrade P (i)
  /-- The projective-bundle map is the sum of pullbacks multiplied by powers of the
  first Chern class of the tautological invertible sheaf. -/
  projectiveBundleMap_apply : ∀ {P X : V} (p : P ⟶ X) (n : ℕ)
      (hp : IsProjectiveBundle p n) (i j : ℤ)
      (a : ∀ r : Fin n,
        Hgrade X (i - 2 * ((r : ℕ) : ℤ))),
    (projectiveBundleMap p n hp i j a : H P) =
      ∑ r : Fin n, pullback p (a r) *
        (firstChernClass P (projectiveBundleLineBundle p n hp) : H P) ^ (r : ℕ)
  /-- Axiom (A3): the projective bundle map is an isomorphism in every bidegree. -/
  axiomA3 : ∀ {P X : V} (p : P ⟶ X) (n : ℕ)
      (hp : IsProjectiveBundle p n) (_hn : 0 < n) (i j : ℤ),
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
  /-- The Künneth map adds cohomological degrees. -/
  kunnethMap_mem : ∀ {X Y : V} {p q : ℤ}
      (a : Hgrade X p) (b : Hgrade Y q),
    kunnethMap X Y (a ⊗ₜ[F] b) ∈ Hgrade (product X Y) (p + q)
  /-- The assertion that an object is the spectrum of the base field. -/
  IsBasePoint : V → Prop
  /-- The scalar map from `F` to bidegree `0` cohomology of the base point. -/
  pointH0Map : ∀ {X}, IsBasePoint X → F →ₗ[F] Hgrade X (0)
  /-- The scalar map to base-point cohomology agrees with the algebra structure. -/
  pointH0Map_apply : ∀ {X} (hX : IsBasePoint X) (a : F),
    (pointH0Map hX a : H X) = algebraMap F (H X) a
  /-- Axiom (A5), base-point clause: `H⁰(Spec F) = F`. -/
  axiomA5_point : ∀ {X} (hX : IsBasePoint X), Function.Bijective (pointH0Map hX)
  axiomA5_point_total : ∀ {X}, IsBasePoint X → Function.Bijective (algebraMap F (H X))
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
  /-- Tate-coordinate form of the cycle-class homomorphism induced by the first
  Chern class. `twistedCycleClass` reconstructs γ : CH^i → H^{2i} ⊗ F(i). -/
  cycleClass : ∀ X, Cycle X →+* H X
  /-- A codimension-i cycle has cohomological degree 2i in Tate coordinates.
  Its externally twisted class is exposed by twistedCycleClass. -/
  cycleClass_mem : ∀ X (i : ℤ) (z : cycleGrade X i),
    cycleClass X z ∈ Hgrade X (2 * i)
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
          ((tensorInterchange F (Hgrade X) (Hgrade Y)
              (Hgrade_isInternal X) (Hgrade_isInternal Y)).symm
            ((LinearEquiv.ofBijective (kunnethMap X X)
                (axiomA5 (nonemptyEquidimensional_isSmoothProjective hX)
                  (nonemptyEquidimensional_isSmoothProjective hX))).symm
                (cycleClass (product X X) (diagonalCycle hX)) ⊗ₜ[F]
              (LinearEquiv.ofBijective (kunnethMap Y Y)
                (axiomA5 (nonemptyEquidimensional_isSmoothProjective hY)
                  (nonemptyEquidimensional_isSmoothProjective hY))).symm
                (cycleClass (product Y Y) (diagonalCycle hY)))))
  /-- Chosen normalized trace witness in Tate coordinates, zero outside degree
  2d. This is supplied data, never chosen from an unproved existence theorem. -/
  integral : ∀ {X d}, IsNonemptyEquidimensional X d → H X →ₗ[F] F
  /-- The total trace vanishes outside cohomological degree `2 * d` (Tate coordinates). -/
  integral_vanishes : ∀ {X d} (hX : IsNonemptyEquidimensional X d)
      (p : ℤ), p ≠ (2 * (d : ℤ)) →
    ∀ a : Hgrade X p, integral hX a = 0
  /-- Axiom (A6): contraction of the diagonal tensor by the trace is the unit. -/
  integral_normalized : ∀ {X d} (hX : IsNonemptyEquidimensional X d),
    contractRight (integral hX)
        ((LinearEquiv.ofBijective (kunnethMap X X)
          (axiomA5 (nonemptyEquidimensional_isSmoothProjective hX)
            (nonemptyEquidimensional_isSmoothProjective hX))).symm
          (cycleClass (product X X) (diagonalCycle hX))) = 1
  /-- Source (A6): existence of a linear functional on the externally twisted
  top degree. Its zero extension contracts the canonical twisted diagonal to 1.
  The supplied coordinate trace above is chosen normalized witness data. -/
  axiomA6 : ∀ {X d} (hX : IsNonemptyEquidimensional X d),
    ∃ ell : Tate.Twist F TateLine (Hgrade X (2 * (d : ℤ))) d →ₗ[F] F,
      contractTwistedRight (extendTopTrace (Hgrade X) (Hgrade_isInternal X) d ell)
        (TensorProduct.map LinearMap.id
          (Tate.trivialization tateLine_rank (H X) (d : ℤ)).symm.toLinearMap
          ((LinearEquiv.ofBijective (kunnethMap X X)
            (axiomA5 (nonemptyEquidimensional_isSmoothProjective hX)
              (nonemptyEquidimensional_isSmoothProjective hX))).symm
            (cycleClass (product X X) (diagonalCycle hX)))) = 1
  /-- The assertion that a morphism is the blowup of a smooth center. -/
  IsBlowupOfSmoothCenter : ∀ {X' X : V}, (X' ⟶ X) → Prop
  /-- Axiom (A7): pullback by the blowup of a smooth center is injective. -/
  axiomA7 : ∀ {X' X : V} (b : X' ⟶ X), IsBlowupOfSmoothCenter b →
    Function.Injective (pullback b)

namespace PreWeilTheory

/-- The source diagonal-class relation (Stacks, lines 55516-55533).
It records the balanced class identity and the canonical point diagonal.
This explicit Prop mixin is an axiom of the abstract layer. Stacks derives
it geometrically from the diagonal in Section 45.14; scheme-level anchoring
is tracked by RL-2194. -/
class HasDiagonalClassRelation
    {F : Type u} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type v} [Category.{v} V] {H Picard Cycle : V → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine V H Picard Cycle) : Prop where
  balanced : ∀ {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) (a : H X),
    T.cycleClass (T.product X X) (T.diagonalCycle hX) * T.pullback (T.fst X X) a =
      T.cycleClass (T.product X X) (T.diagonalCycle hX) * T.pullback (T.snd X X) a
  point : ∀ {X : V} (_hpoint : T.IsBasePoint X) (hX : T.IsNonemptyEquidimensional X 0),
    T.cycleClass (T.product X X) (T.diagonalCycle hX) =
      T.kunnethMap X X ((1 : H X) ⊗ₜ[F] (1 : H X))



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
    tensorInterchange F (T.Hgrade X) (T.Hgrade Y)
        (T.Hgrade_isInternal X) (T.Hgrade_isInternal Y)
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
    (T : PreWeilTheory F TateLine V H Picard Cycle) [T.HasDiagonalClassRelation]
     {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d) (trace : H X →ₗ[F] F) :
    contractRight trace (T.diagonalTensor hX) = 1 → trace = T.integral hX := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

/-- The top-degree coordinate trace. Use twistedTopIntegral for the external tensor-valued domain. -/
noncomputable def topIntegral
    {F : Type u} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type v} [Category.{v} V] {H Picard Cycle : V → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine V H Picard Cycle) {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d) :
    T.Hgrade X (2 * (d : ℤ)) →ₗ[F] F :=
  (T.integral hX).comp (T.Hgrade X (2 * (d : ℤ))).subtype


variable {F : Type u} [Field F] [CharZero F]
variable {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
variable {V : Type v} [Category.{v} V] {H Picard Cycle : V → Type w}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
variable [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
variable (T : PreWeilTheory F TateLine V H Picard Cycle)

/-- External Tate twists of the singly graded total cohomology. -/
abbrev twistedCohomology (_T : PreWeilTheory F TateLine V H Picard Cycle) (X : V) (n : ℤ) := Tate.Twist F TateLine (H X) n

/-- A homogeneous degree with an external Tate twist. There is no inclusion of
all twists as independent summands of H X. -/
abbrev twistedGrade (X : V) (i n : ℤ) := Tate.Twist F TateLine (T.Hgrade X i) n

/-- The Tate shift is derived from genuine tensor powers, not stored as an
identification between subspaces of H X. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def tateTwist (X : V) (i n : ℤ) :
    T.twistedGrade X i n ⊗[F] TateLine ≃ₗ[F] T.twistedGrade X i (n + 1) :=
  Tate.shift T.tateLine_rank (T.Hgrade X i) n

/-- Source D2' reconstructed from its coordinates on the chosen genuine Tate line. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def twistedFirstChernClass (X : V) : Picard X →+ T.twistedGrade X 2 1 :=
  (Tate.trivialization T.tateLine_rank (T.Hgrade X 2) 1).symm.toLinearMap.toAddMonoidHom.comp
    (T.firstChernClass X)

/-- The degreewise cycle class with its source-prescribed external Tate twist. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def twistedCycleClass (X : V) (i : ℤ) : T.cycleGrade X i →+ T.twistedGrade X (2 * i) i :=
  (Tate.trivialization T.tateLine_rank (T.Hgrade X (2 * i)) i).symm.toLinearMap.toAddMonoidHom.comp
    { toFun := fun z ↦ ⟨T.cycleClass X z, T.cycleClass_mem X i z⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b ↦ Subtype.ext ((T.cycleClass X).map_add a b) }

/-- Pullback acts on a fixed external twist. -/
def twistedPullback {X Y : V} (f : X ⟶ Y) (n : ℤ) :
    T.twistedCohomology Y n →ₗ[F] T.twistedCohomology X n :=
  TensorProduct.map (T.pullback f).toLinearMap LinearMap.id

/-- The chosen normalized trace as a functional on externally twisted cohomology.
The stored integral is its coordinate functional, not a functional on a sum of twists. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def twistedIntegral {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) :
    T.twistedCohomology X d →ₗ[F] F :=
  (T.integral hX).comp (Tate.trivialization T.tateLine_rank (H X) d).toLinearMap

/-- The top-degree restriction of the chosen twisted trace. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def twistedTopIntegral {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) :
    T.twistedGrade X (2 * (d : ℤ)) d →ₗ[F] F :=
  (T.twistedIntegral hX).comp (twistedInclusion (T.Hgrade X) (2 * (d : ℤ)) d)

/-- The Künneth map on any two specified external twists. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def twistedKunnethMap (X Y : V) (r s : ℤ) :
    T.twistedCohomology X r ⊗[F] T.twistedCohomology Y s →ₗ[F]
      T.twistedCohomology (T.product X Y) (r + s) :=
  Tate.tensorMap T.tateLine_rank (T.kunnethMap X Y) r s

/-- The diagonal class lives in H(X) ⊗ H(X)(d), with an external twist on the
right factor, rather than in an algebra containing all twists. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def twistedDiagonalTensor {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) :
    H X ⊗[F] T.twistedCohomology X d :=
  TensorProduct.map LinearMap.id
    (Tate.trivialization T.tateLine_rank (H X) d).symm.toLinearMap (T.diagonalTensor hX)

/-- Twisted Künneth sends the derived diagonal tensor to the external
cycle class of the geometric diagonal. -/
theorem twistedDiagonalTensor_spec {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d) :
    TensorProduct.map (T.kunnethMap X X) LinearMap.id
      ((TensorProduct.assoc F (H X) (H X) (Tate.Power F TateLine (d : ℤ))).symm
        (T.twistedDiagonalTensor hX)) =
      twistedInclusion (T.Hgrade (T.product X X)) (2 * (d : ℤ)) d
        (T.twistedCycleClass (T.product X X) d (T.diagonalCycle hX)) := sorry

/-- The supplied trace coordinates give normalized chosen witness data for A6. -/
theorem twistedIntegral_normalized {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d) :
    contractTwistedRight (T.twistedIntegral hX) (T.twistedDiagonalTensor hX) = 1 := sorry

/-- The source's uniqueness assertion compares functionals on the twisted top
cohomological degree, after their canonical zero extension. -/
theorem sourceAxiomA6_unique [T.HasDiagonalClassRelation]
     {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d)
    (ell : T.twistedGrade X (2 * (d : ℤ)) d →ₗ[F] F) :
    contractTwistedRight (extendTopTrace (T.Hgrade X) (T.Hgrade_isInternal X) d ell)
      (T.twistedDiagonalTensor hX) = 1 → ell = T.twistedTopIntegral hX := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

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
    [∀ X, AddCommGroup (Picard X)] extends
      SmoothProjectivePresentation k V dimension product fst snd point CH CHgrade
        cyclePullback cyclePushforward where
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
  Hgrade : ∀ X, ℤ → Submodule F (H X)
  /-- The cohomological-degree summands exhaust total cohomology as an internal direct sum. -/
  Hgrade_isInternal : ∀ X, DirectSum.IsInternal (Hgrade X)
  /-- The unit has cohomological degree zero. -/
  one_mem : ∀ X, (1 : H X) ∈ Hgrade X (0)
  /-- Cup product adds cohomological degrees; external twists are handled by Tate.tensorMap. -/
  mul_mem : ∀ X {p q : ℤ} (a : Hgrade X p) (b : Hgrade X q),
    (a : H X) * b ∈ Hgrade X (p + q)
  /-- Homogeneous cup products satisfy graded commutativity. -/
  gradedComm : ∀ X {i i' : ℤ} (a : Hgrade X (i))
      (b : Hgrade X (i')),
    (a : H X) * b = (-1 : H X) ^ (i * i').natAbs * ((b : H X) * a)
  /-- Data (D1): pullback on total cohomology. -/
  pullback : ∀ {X Y : V}, (X ⟶ Y) → H Y →ₐ[F] H X
  /-- Pullback preserves cohomological degree and Tate twist. -/
  pullback_mem : ∀ {X Y : V} (f : X ⟶ Y) (p : ℤ)
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
  /-- Emptiness is the actual emptiness of the represented scheme. -/
  isEmpty_iff : ∀ X, IsEmpty X ↔ _root_.IsEmpty (scheme.obj X).left
  /-- Axiom (A1), empty clause: an empty object has zero cohomology. -/
  axiomA1_empty : ∀ {X}, IsEmpty X → ∀ a : H X, a = 0
  /-- Axiom (A1), disjoint-union clause: cohomology carries binary disjoint
  unions to products. -/
  axiomA1 : ∀ X Y, Function.Bijective (fun a : H (coproduct X Y) ↦
    (pullback (inl X Y) a, pullback (inr X Y) a))
  /-- Pullback of Picard classes. -/
  picardPullback : ∀ {X Y : V}, (X ⟶ Y) → Picard Y →+ Picard X
  /-- Data (D2'): the first Chern class has bidegree `2`. -/
  firstChernClass : ∀ X, Picard X →+ Hgrade X (2)
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
      (∀ r : Fin n, Hgrade X (i - 2 * ((r : ℕ) : ℤ))) →ₗ[F]
        Hgrade P (i)
  /-- The projective-bundle map is the sum of pullbacks multiplied by powers of
  the tautological first Chern class. -/
  projectiveBundleMap_apply : ∀ {P X : V} (p : P ⟶ X) (n : ℕ)
      (hp : IsProjectiveBundle p n) (i j : ℤ)
      (a : ∀ r : Fin n,
        Hgrade X (i - 2 * ((r : ℕ) : ℤ))),
    (projectiveBundleMap p n hp i j a : H P) =
      ∑ r : Fin n, pullback p (a r) *
        (firstChernClass P (projectiveBundleLineBundle p n hp) : H P) ^ (r : ℕ)
  /-- Axiom (A3): the projective-bundle map is an isomorphism in every bidegree. -/
  axiomA3 : ∀ {P X : V} (p : P ⟶ X) (n : ℕ)
      (hp : IsProjectiveBundle p n) (_hn : 0 < n) (i j : ℤ),
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
  /-- The scalar map to bidegree `0` cohomology of the point. -/
  pointH0Map : F →ₗ[F] Hgrade point (0)
  /-- The scalar map to point cohomology agrees with the algebra structure. -/
  pointH0Map_apply : ∀ a : F,
    (pointH0Map a : H point) = algebraMap F (H point) a
  /-- The exterior-product Künneth map. -/
  kunnethMap : ∀ X Y, H X ⊗[F] H Y →ₗ[F] H (product X Y)
  /-- The Künneth map is pullback to the two factors followed by cup product. -/
  kunnethMap_tmul : ∀ {X Y : V} (a : H X) (b : H Y),
    kunnethMap X Y (a ⊗ₜ[F] b) =
      pullback (fst X Y) a * pullback (snd X Y) b
  /-- The Künneth map adds cohomological degrees. -/
  kunnethMap_mem : ∀ {X Y : V} {p q : ℤ}
      (a : Hgrade X p) (b : Hgrade Y q),
    kunnethMap X Y (a ⊗ₜ[F] b) ∈ Hgrade (product X Y) (p + q)
  /-- Axiom (A5), point clause: `H⁰(point) = F`. -/
  axiomA5_point : Function.Bijective pointH0Map
  axiomA5_point_total : Function.Bijective (algebraMap F (H point))
  /-- Axiom (A5), Künneth clause: exterior product is an isomorphism for every
  pair of smooth projective schemes. -/
  axiomA5 : ∀ X Y, Function.Bijective (kunnethMap X Y)
  /-- Tate-coordinate cycle-class homomorphism; `twistedCycleClass` is the
  source-prescribed external tensor-valued map in each codimension. -/
  cycleClass : ∀ X, CH X →+ H X
  /-- A codimension-i cycle has cohomological degree 2i in Tate coordinates.
  Its externally twisted class is exposed by twistedCycleClass. -/
  cycleClass_mem : ∀ X (i : ℤ) (z : CHgrade X i),
    cycleClass X z ∈ Hgrade X (2 * i)
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
          ((tensorInterchange F (Hgrade X) (Hgrade Y)
              (Hgrade_isInternal X) (Hgrade_isInternal Y)).symm
            ((LinearEquiv.ofBijective (kunnethMap X X) (axiomA5 X X)).symm
                (cycleClass (product X X) (diagonalCycle hX)) ⊗ₜ[F]
              (LinearEquiv.ofBijective (kunnethMap Y Y) (axiomA5 Y Y)).symm
                (cycleClass (product Y Y) (diagonalCycle hY)))))
  /-- Chosen normalized trace witness in Tate coordinates, zero outside degree
  2d. This is supplied data, never chosen from an unproved existence theorem. -/
  integral : ∀ {X d}, IsNonemptyEquidimensional X d → H X →ₗ[F] F
  /-- The total trace vanishes outside cohomological degree `2 * d` (Tate coordinates). -/
  integral_vanishes : ∀ {X d} (hX : IsNonemptyEquidimensional X d)
      (p : ℤ), p ≠ (2 * (d : ℤ)) →
    ∀ a : Hgrade X p, integral hX a = 0
  /-- Axiom (A6): contracting the diagonal class by the normalized trace gives the
  cohomological unit. -/
  integral_normalized : ∀ {X d} (hX : IsNonemptyEquidimensional X d),
    contractRight (integral hX)
        ((LinearEquiv.ofBijective (kunnethMap X X) (axiomA5 X X)).symm
          (cycleClass (product X X) (diagonalCycle hX))) = 1
  /-- Source (A6): existence of a linear functional on the externally twisted
  top degree. Its zero extension contracts the canonical twisted diagonal to 1.
  The supplied coordinate trace above is chosen normalized witness data. -/
  axiomA6 : ∀ {X d} (hX : IsNonemptyEquidimensional X d),
    ∃ ell : Tate.Twist F TateLine (Hgrade X (2 * (d : ℤ))) d →ₗ[F] F,
      contractTwistedRight (extendTopTrace (Hgrade X) (Hgrade_isInternal X) d ell)
        (TensorProduct.map LinearMap.id
          (Tate.trivialization tateLine_rank (H X) (d : ℤ)).symm.toLinearMap
          ((LinearEquiv.ofBijective (kunnethMap X X)
            (axiomA5 X X)).symm
            (cycleClass (product X X) (diagonalCycle hX)))) = 1
  /-- The assertion that a morphism is the blowup of a smooth center. -/
  IsBlowupOfSmoothCenter : ∀ {X' X : V}, (X' ⟶ X) → Prop
  /-- Axiom (A7): pullback by the blowup of a smooth center is injective. -/
  axiomA7 : ∀ {X' X : V} (b : X' ⟶ X),
    IsBlowupOfSmoothCenter b → Function.Injective (pullback b)

namespace SchemePreWeilTheory

section LegacyProjections

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


/- Source-compatible names for the inherited presentation projections.
The stored data and laws belong only to `SmoothProjectivePresentation`. -/
namespace PresentationProjection

variable (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
  cyclePullback cyclePushforward pointCycle H Picard)

abbrev scheme := T.toSmoothProjectivePresentation.scheme
abbrev scheme_fullyFaithful := T.toSmoothProjectivePresentation.scheme_fullyFaithful
abbrev smooth := T.toSmoothProjectivePresentation.smooth
abbrev projective := T.toSmoothProjectivePresentation.projective
abbrev dimension_eq := T.toSmoothProjectivePresentation.dimension_eq
abbrev schemeProduct := T.toSmoothProjectivePresentation.schemeProduct
abbrev scheme_fst := T.toSmoothProjectivePresentation.scheme_fst
abbrev scheme_snd := T.toSmoothProjectivePresentation.scheme_snd
abbrev schemePoint := T.toSmoothProjectivePresentation.schemePoint
abbrev structureMorphism := T.toSmoothProjectivePresentation.structureMorphism
abbrev scheme_structureMorphism := T.toSmoothProjectivePresentation.scheme_structureMorphism
abbrev scheme_essentiallySurjective := T.toSmoothProjectivePresentation.scheme_essentiallySurjective
abbrev cyclePullback_id := T.toSmoothProjectivePresentation.cyclePullback_id
abbrev cyclePullback_comp {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  T.toSmoothProjectivePresentation.cyclePullback_comp f g
abbrev cyclePushforward_id := T.toSmoothProjectivePresentation.cyclePushforward_id
abbrev cyclePushforward_comp {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  T.toSmoothProjectivePresentation.cyclePushforward_comp f g

end PresentationProjection

export PresentationProjection (scheme scheme_fullyFaithful smooth projective dimension_eq
  schemeProduct scheme_fst scheme_snd schemePoint structureMorphism scheme_structureMorphism
  scheme_essentiallySurjective cyclePullback_id cyclePullback_comp cyclePushforward_id
  cyclePushforward_comp)

end LegacyProjections

/-- The source diagonal-class relation (Stacks, lines 55516-55533).
It records the balanced class identity and the canonical point diagonal.
This explicit Prop mixin is an axiom of the abstract layer. Stacks derives
it geometrically from the diagonal in Section 45.14; scheme-level anchoring
is tracked by RL-2194. -/
class HasDiagonalClassRelation
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
      cyclePullback cyclePushforward pointCycle H Picard) : Prop where
  balanced : ∀ {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) (a : H X),
    T.cycleClass (product X X) (T.diagonalCycle hX) * T.pullback (fst X X) a =
      T.cycleClass (product X X) (T.diagonalCycle hX) * T.pullback (snd X X) a
  point : ∀ hpoint : T.IsNonemptyEquidimensional point 0,
    T.cycleClass (product point point) (T.diagonalCycle hpoint) =
      T.kunnethMap point point ((1 : H point) ⊗ₜ[F] (1 : H point))



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
    tensorInterchange F (T.Hgrade X) (T.Hgrade Y)
        (T.Hgrade_isInternal X) (T.Hgrade_isInternal Y)
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
      cyclePullback cyclePushforward pointCycle H Picard) [T.HasDiagonalClassRelation]
    {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (trace : H X →ₗ[F] F) :
    contractRight trace (T.diagonalTensor hX) = 1 → trace = T.integral hX := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry


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


variable (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
  cyclePullback cyclePushforward pointCycle H Picard)

/-- External Tate twists of the singly graded total cohomology. -/
abbrev twistedCohomology
    (_T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard) (X : V) (n : ℤ) := Tate.Twist F TateLine (H X) n

/-- A homogeneous degree with an external Tate twist. There is no inclusion of
all twists as independent summands of H X. -/
abbrev twistedGrade (X : V) (i n : ℤ) := Tate.Twist F TateLine (T.Hgrade X i) n

/-- The Tate shift is derived from genuine tensor powers, not stored as an
identification between subspaces of H X. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def tateTwist (X : V) (i n : ℤ) :
    T.twistedGrade X i n ⊗[F] TateLine ≃ₗ[F] T.twistedGrade X i (n + 1) :=
  Tate.shift T.tateLine_rank (T.Hgrade X i) n

/-- Source D2' reconstructed from its coordinates on the chosen genuine Tate line. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def twistedFirstChernClass (X : V) : Picard X →+ T.twistedGrade X 2 1 :=
  (Tate.trivialization T.tateLine_rank (T.Hgrade X 2) 1).symm.toLinearMap.toAddMonoidHom.comp
    (T.firstChernClass X)

/-- The degreewise cycle class with its source-prescribed external Tate twist. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def twistedCycleClass (X : V) (i : ℤ) : CHgrade X i →+ T.twistedGrade X (2 * i) i :=
  (Tate.trivialization T.tateLine_rank (T.Hgrade X (2 * i)) i).symm.toLinearMap.toAddMonoidHom.comp
    { toFun := fun z ↦ ⟨T.cycleClass X z, T.cycleClass_mem X i z⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b ↦ Subtype.ext ((T.cycleClass X).map_add a b) }

/-- Pullback acts on a fixed external twist. -/
def twistedPullback {X Y : V} (f : X ⟶ Y) (n : ℤ) :
    T.twistedCohomology Y n →ₗ[F] T.twistedCohomology X n :=
  TensorProduct.map (T.pullback f).toLinearMap LinearMap.id

/-- The chosen normalized trace as a functional on externally twisted cohomology.
The stored integral is its coordinate functional, not a functional on a sum of twists. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def twistedIntegral {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) :
    T.twistedCohomology X d →ₗ[F] F :=
  (T.integral hX).comp (Tate.trivialization T.tateLine_rank (H X) d).toLinearMap

/-- The top-degree restriction of the chosen twisted trace. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def twistedTopIntegral {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) :
    T.twistedGrade X (2 * (d : ℤ)) d →ₗ[F] F :=
  (T.twistedIntegral hX).comp (twistedInclusion (T.Hgrade X) (2 * (d : ℤ)) d)

/-- The Künneth map on any two specified external twists. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def twistedKunnethMap (X Y : V) (r s : ℤ) :
    T.twistedCohomology X r ⊗[F] T.twistedCohomology Y s →ₗ[F]
      T.twistedCohomology (product X Y) (r + s) :=
  Tate.tensorMap T.tateLine_rank (T.kunnethMap X Y) r s

/-- The diagonal class lives in H(X) ⊗ H(X)(d), with an external twist on the
right factor, rather than in an algebra containing all twists. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def twistedDiagonalTensor {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) :
    H X ⊗[F] T.twistedCohomology X d :=
  TensorProduct.map LinearMap.id
    (Tate.trivialization T.tateLine_rank (H X) d).symm.toLinearMap (T.diagonalTensor hX)

/-- Twisted Künneth sends the derived diagonal tensor to the external
cycle class of the geometric diagonal. -/
theorem twistedDiagonalTensor_spec {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d) :
    TensorProduct.map (T.kunnethMap X X) LinearMap.id
      ((TensorProduct.assoc F (H X) (H X) (Tate.Power F TateLine (d : ℤ))).symm
        (T.twistedDiagonalTensor hX)) =
      twistedInclusion (T.Hgrade (product X X)) (2 * (d : ℤ)) d
        (T.twistedCycleClass (product X X) d (T.diagonalCycle hX)) := sorry

/-- The supplied trace coordinates give normalized chosen witness data for A6. -/
theorem twistedIntegral_normalized {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d) :
    contractTwistedRight (T.twistedIntegral hX) (T.twistedDiagonalTensor hX) = 1 := sorry

/-- The source's uniqueness assertion compares functionals on the twisted top
cohomological degree, after their canonical zero extension. -/
theorem sourceAxiomA6_unique [T.HasDiagonalClassRelation]
     {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d)
    (ell : T.twistedGrade X (2 * (d : ℤ)) d →ₗ[F] F) :
    contractTwistedRight (extendTopTrace (T.Hgrade X) (T.Hgrade_isInternal X) d ell)
      (T.twistedDiagonalTensor hX) = 1 → ell = T.twistedTopIntegral hX := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

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
    Function.Bijective (T.kunnethMap X Y) := T.axiomA5 X Y

/-- Integration on a product is the tensor-product trace transported across the
Künneth isomorphism. -/
theorem integral_eq_tensorProductTrace_of_axiomsA1ToA7
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard) [T.HasDiagonalClassRelation]
    (X Y : V) {d e : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y e) :
    T.integral (T.product_isNonemptyEquidimensional hX hY) =
      tensorProductTrace (T.kunnethMap X Y)
        (kunnethMap_bijective_of_axiomsA1ToA7 T X Y)
        (T.integral hX) (T.integral hY) := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

/-- The integral of an exterior product is the product of the two integrals. -/
theorem integral_kunnethMap_tmul_of_axiomsA1ToA7
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard) [T.HasDiagonalClassRelation]
    (X Y : V) {d e : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y e) (a : H X) (b : H Y) :
    T.integral (T.product_isNonemptyEquidimensional hX hY)
        (T.kunnethMap X Y (a ⊗ₜ[F] b)) =
      T.integral hX a * T.integral hY b := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

/-- The product-trace identity on the actual external dimension twists. -/
theorem twistedIntegral_kunnethMap_tmul_of_axiomsA1ToA7
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard) [T.HasDiagonalClassRelation]
    {X Y : V} {d e : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y e)
    (a : T.twistedCohomology X d) (b : T.twistedCohomology Y e) :
    T.twistedIntegral (T.product_isNonemptyEquidimensional hX hY)
        (T.twistedKunnethMap X Y d e (a ⊗ₜ[F] b)) =
      T.twistedIntegral hX a * T.twistedIntegral hY b := by
  have hdiagonal : T.HasDiagonalClassRelation := inferInstance
  sorry

end WeilCohomology
