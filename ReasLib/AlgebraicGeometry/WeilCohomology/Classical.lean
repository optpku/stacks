/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import ReasLib.AlgebraicGeometry.WeilCohomology.SmoothProjective

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u v w x y z

namespace WeilCohomology

/-- A classical Weil cohomology theory on an abstract category of smooth projective
`k`-varieties. The total cohomology algebras and Chow rings are internally graded;
the displayed maps give the cohomological data, while the remaining fields are the
Poincaré-duality, Künneth, and cycle-class axioms. -/
structure ClassicalTheory
    (k : Type u) [Field k] [IsAlgClosed k]
    (F : Type v) [Field F] [CharZero F]
    (V : Type w) [Category.{z} V]
    (dimension : V → ℕ) (product : V → V → V)
    (fst : ∀ X Y, product X Y ⟶ X) (snd : ∀ X Y, product X Y ⟶ Y)
    (point : V) (H : V → Type x) (CH : V → Type y)
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
    (Hgrade : ∀ X, ℤ → Submodule F (H X))
    (CHgrade : ∀ X, ℤ → Submodule ℤ (CH X))
    [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
    (cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X)
    (cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y)
    (pointCycle : CHgrade point 0) where
  /-- The smooth-projective geometric and Chow-theoretic presentation over `k`. -/
  geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
    cyclePullback cyclePushforward pointCycle
  /-- Contravariant pullback as a degree-preserving algebra homomorphism. -/
  pullback : ∀ {X Y : V}, (X ⟶ Y) → Hgrade Y →ₐᵍ[F] Hgrade X
  /-- Pullback by an identity morphism is the identity. -/
  pullback_id : ∀ X, pullback (𝟙 X) = GradedAlgHom.id F (Hgrade X)
  /-- Pullback reverses composition. -/
  pullback_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
    pullback (f ≫ g) = (pullback f).comp (pullback g)
  /-- Homogeneous cup products satisfy graded commutativity. -/
  gradedComm : ∀ X {i j : ℤ} (a : Hgrade X i) (b : Hgrade X j),
    (a : H X) * b = (-1 : H X) ^ (i * j).natAbs * ((b : H X) * a)
  /-- The additive cycle-class map on total Chow and cohomology groups. -/
  cycleClass : ∀ X, CH X →+ H X
  /-- A codimension-`i` cycle has cohomological degree `2 * i`. -/
  cycleClass_mem : ∀ X (i : ℤ) (alpha : CHgrade X i),
    cycleClass X alpha ∈ Hgrade X (2 * i)
  /-- The trace, extended by zero from top degree to total cohomology. -/
  integral : ∀ X, H X →ₗ[F] F
  /-- The total trace vanishes away from degree `2 * dimension X`. -/
  integral_vanishes : ∀ X (i : ℤ), i ≠ 2 * (dimension X : ℤ) →
    ∀ a : Hgrade X i, integral X a = 0
  /-- Each homogeneous cohomology group is finite-dimensional over `F`. -/
  finiteDimensional : ∀ X (i : ℤ), Module.Finite F (Hgrade X i)
  /-- The linear map associated to the Poincaré pairing in complementary degrees. -/
  poincarePairing : ∀ X (i : ℤ),
    Hgrade X (2 * (dimension X : ℤ) - i) →ₗ[F] (Hgrade X i →ₗ[F] F)
  /-- The Poincaré pairing evaluates by cup product followed by the trace. -/
  poincarePairing_apply : ∀ X (i : ℤ)
      (a : Hgrade X (2 * (dimension X : ℤ) - i)) (b : Hgrade X i),
    poincarePairing X i a b = integral X ((b : H X) * a)
  /-- The Poincaré pairing is perfect in every degree. -/
  poincarePairing_bijective : ∀ X (i : ℤ), Function.Bijective (poincarePairing X i)
  /-- Cohomology vanishes outside degrees from `0` through `2 * dimension X`. -/
  cohomology_vanishes : ∀ X (i : ℤ),
    i < 0 ∨ 2 * (dimension X : ℤ) < i → Hgrade X i = ⊥
  /-- The trace restricts to an isomorphism on top-degree cohomology. -/
  integral_top_bijective : ∀ X, Function.Bijective
    ((integral X).comp (Hgrade X (2 * (dimension X : ℤ))).subtype)
  /-- The cohomological pushforward characterized by Poincaré duality. -/
  pushforward : ∀ {X Y : V}, (X ⟶ Y) → H X →ₗ[F] H Y
  /-- Pushforward has the degree shift prescribed by the dimensions. -/
  pushforward_mem : ∀ {X Y : V} (f : X ⟶ Y) (i : ℤ) (a : Hgrade X i),
    pushforward f a ∈ Hgrade Y (i + 2 * ((dimension Y : ℤ) - dimension X))
  /-- Pushforward is adjoint to pullback for the Poincaré pairings. -/
  pushforward_spec : ∀ {X Y : V} (f : X ⟶ Y) (i : ℤ)
      (a : Hgrade X (2 * (dimension X : ℤ) - i)) (b : Hgrade Y i),
    integral X (pullback f b * a) = integral Y ((b : H Y) * pushforward f a)
  /-- The exterior-product map appearing in the Künneth formula. -/
  kunnethMap : ∀ X Y, H X ⊗[F] H Y →ₗ[F] H (product X Y)
  /-- On pure tensors, the Künneth map is the cup product of the two pullbacks. -/
  kunnethMap_tmul : ∀ X Y (a : H X) (b : H Y),
    kunnethMap X Y (a ⊗ₜ[F] b) = pullback (fst X Y) a * pullback (snd X Y) b
  /-- The Künneth map adds the degrees of homogeneous inputs. -/
  kunnethMap_mem : ∀ X Y (i j : ℤ) (a : Hgrade X i) (b : Hgrade Y j),
    kunnethMap X Y (a ⊗ₜ[F] b) ∈ Hgrade (product X Y) (i + j)
  /-- The Künneth map is an isomorphism of graded vector spaces. -/
  kunnethMap_bijective : ∀ X Y, Function.Bijective (kunnethMap X Y)
  /-- The supplied Chow pushforward has the codimension shift prescribed by dimensions. -/
  cyclePushforward_mem : ∀ {X Y : V} (f : X ⟶ Y) (i : ℤ) (alpha : CHgrade X i),
    cyclePushforward f alpha ∈ CHgrade Y (i + ((dimension Y : ℤ) - dimension X))
  /-- Cycle classes commute with pullback. -/
  cycleClass_pullback : ∀ {X Y : V} (f : X ⟶ Y) (beta : CH Y),
    cycleClass X (cyclePullback f beta) = pullback f (cycleClass Y beta)
  /-- Cycle classes commute with pushforward. -/
  cycleClass_pushforward : ∀ {X Y : V} (f : X ⟶ Y) (alpha : CH X),
    cycleClass Y (cyclePushforward f alpha) = pushforward f (cycleClass X alpha)
  /-- Cycle classes carry intersection products to cup products. -/
  cycleClass_mul : ∀ X (alpha beta : CH X),
    cycleClass X (alpha * beta) = cycleClass X alpha * cycleClass X beta
  /-- The class of the point is normalized to have trace `1`. -/
  point_normalization : integral point (cycleClass point pointCycle) = 1

namespace ClassicalTheory

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {F : Type v} [Field F] [CharZero F]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {H : V → Type x} {CH : V → Type y}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
variable {Hgrade : ∀ X, ℤ → Submodule F (H X)}
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
variable [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
variable {pointCycle : CHgrade point 0}

/-- Build a classical Weil cohomology theory from its explicit maps and the atomic
Poincaré-duality, Künneth, and cycle-class laws. -/
def ofAxioms
    (geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle)
    (pullback : ∀ {X Y : V}, (X ⟶ Y) → Hgrade Y →ₐᵍ[F] Hgrade X)
    (pullback_id : ∀ X, pullback (𝟙 X) = GradedAlgHom.id F (Hgrade X))
    (pullback_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
      pullback (f ≫ g) = (pullback f).comp (pullback g))
    (gradedComm : ∀ X {i j : ℤ} (a : Hgrade X i) (b : Hgrade X j),
      (a : H X) * b = (-1 : H X) ^ (i * j).natAbs * ((b : H X) * a))
    (cycleClass : ∀ X, CH X →+ H X)
    (cycleClass_mem : ∀ X (i : ℤ) (alpha : CHgrade X i),
      cycleClass X alpha ∈ Hgrade X (2 * i))
    (integral : ∀ X, H X →ₗ[F] F)
    (integral_vanishes : ∀ X (i : ℤ), i ≠ 2 * (dimension X : ℤ) →
      ∀ a : Hgrade X i, integral X a = 0)
    (finiteDimensional : ∀ X (i : ℤ), Module.Finite F (Hgrade X i))
    (poincarePairing : ∀ X (i : ℤ),
      Hgrade X (2 * (dimension X : ℤ) - i) →ₗ[F] (Hgrade X i →ₗ[F] F))
    (poincarePairing_apply : ∀ X (i : ℤ)
        (a : Hgrade X (2 * (dimension X : ℤ) - i)) (b : Hgrade X i),
      poincarePairing X i a b = integral X ((b : H X) * a))
    (poincarePairing_bijective : ∀ X (i : ℤ), Function.Bijective (poincarePairing X i))
    (cohomology_vanishes : ∀ X (i : ℤ),
      i < 0 ∨ 2 * (dimension X : ℤ) < i → Hgrade X i = ⊥)
    (integral_top_bijective : ∀ X, Function.Bijective
      ((integral X).comp (Hgrade X (2 * (dimension X : ℤ))).subtype))
    (pushforward : ∀ {X Y : V}, (X ⟶ Y) → H X →ₗ[F] H Y)
    (pushforward_mem : ∀ {X Y : V} (f : X ⟶ Y) (i : ℤ) (a : Hgrade X i),
      pushforward f a ∈ Hgrade Y (i + 2 * ((dimension Y : ℤ) - dimension X)))
    (pushforward_spec : ∀ {X Y : V} (f : X ⟶ Y) (i : ℤ)
        (a : Hgrade X (2 * (dimension X : ℤ) - i)) (b : Hgrade Y i),
      integral X (pullback f b * a) = integral Y ((b : H Y) * pushforward f a))
    (kunnethMap : ∀ X Y, H X ⊗[F] H Y →ₗ[F] H (product X Y))
    (kunnethMap_tmul : ∀ X Y (a : H X) (b : H Y),
      kunnethMap X Y (a ⊗ₜ[F] b) = pullback (fst X Y) a * pullback (snd X Y) b)
    (kunnethMap_mem : ∀ X Y (i j : ℤ) (a : Hgrade X i) (b : Hgrade Y j),
      kunnethMap X Y (a ⊗ₜ[F] b) ∈ Hgrade (product X Y) (i + j))
    (kunnethMap_bijective : ∀ X Y, Function.Bijective (kunnethMap X Y))
    (cyclePushforward_mem : ∀ {X Y : V} (f : X ⟶ Y) (i : ℤ)
        (alpha : CHgrade X i),
      cyclePushforward f alpha ∈ CHgrade Y (i + ((dimension Y : ℤ) - dimension X)))
    (cycleClass_pullback : ∀ {X Y : V} (f : X ⟶ Y) (beta : CH Y),
      cycleClass X (cyclePullback f beta) = pullback f (cycleClass Y beta))
    (cycleClass_pushforward : ∀ {X Y : V} (f : X ⟶ Y) (alpha : CH X),
      cycleClass Y (cyclePushforward f alpha) = pushforward f (cycleClass X alpha))
    (cycleClass_mul : ∀ X (alpha beta : CH X),
      cycleClass X (alpha * beta) = cycleClass X alpha * cycleClass X beta)
    (point_normalization : integral point (cycleClass point pointCycle) = 1) :
    ClassicalTheory k F V dimension product fst snd point H CH Hgrade CHgrade
      cyclePullback cyclePushforward pointCycle where
  geometry := geometry
  pullback := pullback
  pullback_id := pullback_id
  pullback_comp := pullback_comp
  gradedComm := gradedComm
  cycleClass := cycleClass
  cycleClass_mem := cycleClass_mem
  integral := integral
  integral_vanishes := integral_vanishes
  finiteDimensional := finiteDimensional
  poincarePairing := poincarePairing
  poincarePairing_apply := poincarePairing_apply
  poincarePairing_bijective := poincarePairing_bijective
  cohomology_vanishes := cohomology_vanishes
  integral_top_bijective := integral_top_bijective
  pushforward := pushforward
  pushforward_mem := pushforward_mem
  pushforward_spec := pushforward_spec
  kunnethMap := kunnethMap
  kunnethMap_tmul := kunnethMap_tmul
  kunnethMap_mem := kunnethMap_mem
  kunnethMap_bijective := kunnethMap_bijective
  cyclePushforward_mem := cyclePushforward_mem
  cycleClass_pullback := cycleClass_pullback
  cycleClass_pushforward := cycleClass_pushforward
  cycleClass_mul := cycleClass_mul
  point_normalization := point_normalization

/-- A linear map satisfying the Poincaré adjunction formula is the stored
cohomological pushforward. -/
theorem pushforward_unique
    (T : ClassicalTheory k F V dimension product fst snd point H CH Hgrade CHgrade
      cyclePullback cyclePushforward pointCycle)
    {X Y : V} (f : X ⟶ Y) (q : H X →ₗ[F] H Y)
    (q_mem : ∀ (i : ℤ) (a : Hgrade X i),
      q a ∈ Hgrade Y (i + 2 * ((dimension Y : ℤ) - dimension X)))
    (q_adjoint : ∀ (i : ℤ)
        (a : Hgrade X (2 * (dimension X : ℤ) - i)) (b : Hgrade Y i),
      T.integral X (T.pullback f b * a) = T.integral Y ((b : H Y) * q a)) :
    q = T.pushforward f := sorry

/-- Poincaré duality consists of finite-dimensional homogeneous cohomology, the
cup-trace pairing, its perfectness, boundedness, and the top-degree trace isomorphism. -/
theorem poincareDuality_spec
    (T : ClassicalTheory k F V dimension product fst snd point H CH Hgrade CHgrade
      cyclePullback cyclePushforward pointCycle) :
    (∀ X (i : ℤ), Module.Finite F (Hgrade X i)) ∧
    (∀ X (i : ℤ) (a : Hgrade X (2 * (dimension X : ℤ) - i)) (b : Hgrade X i),
      T.poincarePairing X i a b = T.integral X ((b : H X) * a)) ∧
    (∀ X (i : ℤ), Function.Bijective (T.poincarePairing X i)) ∧
    (∀ X (i : ℤ), i < 0 ∨ 2 * (dimension X : ℤ) < i → Hgrade X i = ⊥) ∧
    (∀ X, Function.Bijective
      ((T.integral X).comp (Hgrade X (2 * (dimension X : ℤ))).subtype)) := sorry

/-- The Künneth formula identifies the exterior-product map on pure tensors,
preserves the sum of homogeneous degrees, and makes that map bijective. -/
theorem kunnethFormula_spec
    (T : ClassicalTheory k F V dimension product fst snd point H CH Hgrade CHgrade
      cyclePullback cyclePushforward pointCycle) :
    (∀ X Y (a : H X) (b : H Y),
      T.kunnethMap X Y (a ⊗ₜ[F] b) =
        T.pullback (fst X Y) a * T.pullback (snd X Y) b) ∧
    (∀ X Y (i j : ℤ) (a : Hgrade X i) (b : Hgrade Y j),
      T.kunnethMap X Y (a ⊗ₜ[F] b) ∈ Hgrade (product X Y) (i + j)) ∧
    (∀ X Y, Function.Bijective (T.kunnethMap X Y)) := sorry

/-- Cycle classes commute with pullback, pushforward, and products, and the
class of the point has trace one. -/
theorem cycleClassCompatibility_spec
    (T : ClassicalTheory k F V dimension product fst snd point H CH Hgrade CHgrade
      cyclePullback cyclePushforward pointCycle) :
    (∀ {X Y : V} (f : X ⟶ Y) (beta : CH Y),
      T.cycleClass X (cyclePullback f beta) = T.pullback f (T.cycleClass Y beta)) ∧
    (∀ {X Y : V} (f : X ⟶ Y) (alpha : CH X),
      T.cycleClass Y (cyclePushforward f alpha) = T.pushforward f (T.cycleClass X alpha)) ∧
    (∀ X (alpha beta : CH X),
      T.cycleClass X (alpha * beta) = T.cycleClass X alpha * T.cycleClass X beta) ∧
    T.integral point (T.cycleClass point pointCycle) = 1 := sorry

end ClassicalTheory

end WeilCohomology
