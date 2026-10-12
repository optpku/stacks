/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.DirectSum.Module
public import ReasLib.Topology.KrullDimension.Equidimensional
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.AlgebraicGeometry.WeilCohomology.Classical

@[expose] public section

noncomputable section

universe u v w x y z

namespace WeilCohomology

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct

/-- A classical Weil cohomology theory on a scheme-valued presentation over an arbitrary field. -/
structure SchemeClassicalTheory
    (k : Type u) [Field k]
    (F : Type v) [Field F] [CharZero F]
    (TateLine : Type w) [AddCommGroup TateLine] [Module F TateLine]
    (V : Type w) [Category.{z} V]
    (dimension : V → ℕ) (product : V → V → V)
    (fst : ∀ X Y, product X Y ⟶ X) (snd : ∀ X Y, product X Y ⟶ Y)
    (point : V) (H : V → Type x) (CH : V → Type y)
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
    (Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X))
    (CHgrade : ∀ X, ℤ → Submodule ℤ (CH X))
    [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
    (cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X)
    (cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y) where
  /-- The functor realizing the abstract domain as schemes over `k`. -/
  scheme : V ⥤ SchemeOverField k
  /-- Morphisms in the presentation are precisely morphisms of represented schemes. -/
  scheme_fullyFaithful : scheme.FullyFaithful
  /-- Every represented scheme is smooth over `k`. -/
  smooth : ∀ X, Smooth (scheme.obj X).hom
  /-- Every represented scheme is projective over `k`. -/
  projective : ∀ X, Projective (scheme.obj X).hom
  /-- The specified dimension agrees with geometric Krull dimension on nonempty objects. -/
  dimension_eq : ∀ X, Nonempty (scheme.obj X).left →
    topologicalKrullDim (scheme.obj X).left = (dimension X : WithBot ℕ∞)
  /-- The specified product represents the fibre product over `Spec(k)`. -/
  schemeProduct : ∀ X Y, scheme.obj (product X Y) ≅ scheme.obj X ⨯ scheme.obj Y
  /-- The first product projection is represented by `fst`. -/
  scheme_fst : ∀ X Y, scheme.map (fst X Y) =
    (schemeProduct X Y).hom ≫ Limits.prod.fst
  /-- The second product projection is represented by `snd`. -/
  scheme_snd : ∀ X Y, scheme.map (snd X Y) =
    (schemeProduct X Y).hom ≫ Limits.prod.snd
  /-- The distinguished point represents `Spec(k)`. -/
  schemePoint : scheme.obj point ≅ Over.mk (𝟙 (Spec (CommRingCat.of k)))
  /-- The structure morphism from each represented scheme to the point. -/
  structureMorphism : ∀ X, X ⟶ point
  /-- The represented structure morphism is the canonical map to `Spec(k)`. -/
  scheme_structureMorphism : ∀ X,
    scheme.map (structureMorphism X) ≫ schemePoint.hom =
      Over.homMk (scheme.obj X).hom
  /-- Every smooth projective scheme over `k` is represented by an object of `V`. -/
  scheme_essentiallySurjective : ∀ (S : SchemeOverField k)
    [Smooth S.hom] [Projective S.hom],
    ∃ X : V, Nonempty (scheme.obj X ≅ S)
  /-- Chow pullback by an identity is the identity. -/
  cyclePullback_id : ∀ X, cyclePullback (𝟙 X) = GradedAlgHom.id ℤ (CHgrade X)
  /-- Chow pullback reverses composition. -/
  cyclePullback_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
    cyclePullback (f ≫ g) = (cyclePullback f).comp (cyclePullback g)
  /-- Chow pushforward by an identity is the identity. -/
  cyclePushforward_id : ∀ X, cyclePushforward (𝟙 X) = AddMonoidHom.id (CH X)
  /-- Chow pushforward preserves composition. -/
  cyclePushforward_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
    cyclePushforward (f ≫ g) = (cyclePushforward g).comp (cyclePushforward f)
  /-- The predicate for nonempty equidimensional represented schemes of dimension `d`. -/
  IsNonemptyEquidimensional : V → ℕ → Prop
  /-- The nonempty-equidimensional predicate has its geometric meaning. -/
  nonemptyEquidimensional_iff : ∀ {X d}, IsNonemptyEquidimensional X d ↔
    Nonempty (scheme.obj X).left ∧ EquidimensionalSpace (scheme.obj X).left ∧
      dimension X = d
  /-- Products of nonempty equidimensional schemes remain so, with dimensions adding. -/
  product_isNonemptyEquidimensional : ∀ {X Y d e},
    IsNonemptyEquidimensional X d → IsNonemptyEquidimensional Y e →
      IsNonemptyEquidimensional (product X Y) (d + e)
  /-- The distinguished point is nonempty and equidimensional of dimension zero. -/
  point_isNonemptyEquidimensional : IsNonemptyEquidimensional point 0
  /-- Pullback of the point fundamental class is the fundamental class of every object. -/
  fundamentalClass_pullback : ∀ X,
    cyclePullback (structureMorphism X) (1 : CHgrade point 0) = 1
  /-- The Chow class of a closed point on a nonempty equidimensional scheme. -/
  closedPointClass : ∀ {X d}, IsNonemptyEquidimensional X d →
    closedPoints (scheme.obj X).left → CHgrade X d
  /-- Pushforward of a closed-point class records the residue-field degree. -/
  closedPointClass_pushforward : ∀ {X d} (hX : IsNonemptyEquidimensional X d)
      (x : closedPoints (scheme.obj X).left)
      [FiniteDimensional k ((scheme.obj X).left.residueField x)],
    cyclePushforward (structureMorphism X) (closedPointClass hX x) =
      (Module.finrank k ((scheme.obj X).left.residueField x) : ℤ) •
        (1 : CHgrade point 0)
  /-- The chosen Tate line has dimension one. -/
  tateLine_rank : Module.finrank F TateLine = 1
  /-- The bigraded cohomology summands exhaust total cohomology. -/
  Hgrade_isInternal : ∀ X, DirectSum.IsInternal (Hgrade X)
  /-- Tensoring with the Tate line raises the twist index by one. -/
  tateTwist : ∀ X i j,
    Hgrade X (i, j) ⊗[F] TateLine ≃ₗ[F] Hgrade X (i, j + 1)
  /-- Contravariant pullback on bigraded cohomology. -/
  pullback : ∀ {X Y : V}, (X ⟶ Y) → Hgrade Y →ₐᵍ[F] Hgrade X
  /-- Pullback by an identity morphism is the identity. -/
  pullback_id : ∀ X, pullback (𝟙 X) = GradedAlgHom.id F (Hgrade X)
  /-- Pullback reverses composition. -/
  pullback_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
    pullback (f ≫ g) = (pullback f).comp (pullback g)
  /-- Homogeneous cup products satisfy graded commutativity in cohomological degree. -/
  gradedComm : ∀ X {i i' j j' : ℤ} (a : Hgrade X (i, j))
      (b : Hgrade X (i', j')),
    (a : H X) * b = (-1 : H X) ^ (i * i').natAbs * ((b : H X) * a)
  /-- The additive cycle-class map on total Chow and cohomology groups. -/
  cycleClass : ∀ X, CH X →+ H X
  /-- A codimension-`i` cycle has bidegree `(2 * i, i)`. -/
  cycleClass_mem : ∀ X (i : ℤ) (alpha : CHgrade X i),
    cycleClass X alpha ∈ Hgrade X (2 * i, i)
  /-- The trace on a nonempty equidimensional scheme. -/
  integral : ∀ {X d}, IsNonemptyEquidimensional X d → H X →ₗ[F] F
  /-- The trace vanishes away from top bidegree. -/
  integral_vanishes : ∀ {X d} (hX : IsNonemptyEquidimensional X d)
      (p : ℤ × ℤ), p ≠ (2 * (d : ℤ), (d : ℤ)) →
    ∀ a : Hgrade X p, integral hX a = 0
  /-- Every homogeneous cohomology group is finite-dimensional. -/
  finiteDimensional : ∀ {X d}, IsNonemptyEquidimensional X d →
    ∀ p : ℤ × ℤ, Module.Finite F (Hgrade X p)
  /-- The linear map associated to the Poincare pairing. -/
  poincarePairing : ∀ {X d} (hX : IsNonemptyEquidimensional X d) (i j : ℤ),
    Hgrade X (2 * (d : ℤ) - i, (d : ℤ) - j) →ₗ[F]
      (Hgrade X (i, j) →ₗ[F] F)
  /-- The Poincare pairing is cup product followed by the trace. -/
  poincarePairing_apply : ∀ {X d} (hX : IsNonemptyEquidimensional X d) (i j : ℤ)
      (a : Hgrade X (2 * (d : ℤ) - i, (d : ℤ) - j))
      (b : Hgrade X (i, j)),
    poincarePairing hX i j a b = integral hX ((b : H X) * a)
  /-- The Poincare pairing is perfect in every bidegree. -/
  poincarePairing_bijective : ∀ {X d} (hX : IsNonemptyEquidimensional X d)
      (i j : ℤ), Function.Bijective (poincarePairing hX i j)
  /-- Cohomological pushforward between nonempty equidimensional schemes. -/
  pushforward : ∀ {X Y d e}, IsNonemptyEquidimensional X d →
    IsNonemptyEquidimensional Y e → (X ⟶ Y) → H X →ₗ[F] H Y
  /-- Pushforward has the bidegree shift prescribed by dimensions. -/
  pushforward_mem : ∀ {X Y d e} (hX : IsNonemptyEquidimensional X d)
      (hY : IsNonemptyEquidimensional Y e) (f : X ⟶ Y) (i j : ℤ)
      (a : Hgrade X (i, j)),
    pushforward hX hY f a ∈
      Hgrade Y (i + 2 * ((e : ℤ) - d), j + ((e : ℤ) - d))
  /-- Pushforward is adjoint to pullback for the Poincare pairings. -/
  pushforward_spec : ∀ {X Y d e} (hX : IsNonemptyEquidimensional X d)
      (hY : IsNonemptyEquidimensional Y e) (f : X ⟶ Y) (a : H X) (b : H Y),
    integral hX (pullback f b * a) = integral hY (b * pushforward hX hY f a)
  /-- The exterior-product map in the Kunneth formula. -/
  kunnethMap : ∀ X Y, H X ⊗[F] H Y →ₗ[F] H (product X Y)
  /-- On pure tensors, the Kunneth map is the product of pullbacks. -/
  kunnethMap_tmul : ∀ X Y (a : H X) (b : H Y),
    kunnethMap X Y (a ⊗ₜ[F] b) = pullback (fst X Y) a * pullback (snd X Y) b
  /-- The Kunneth map adds both grading indices. -/
  kunnethMap_mem : ∀ X Y (p q : ℤ × ℤ) (a : Hgrade X p) (b : Hgrade Y q),
    kunnethMap X Y (a ⊗ₜ[F] b) ∈ Hgrade (product X Y) (p + q)
  /-- The Kunneth map is bijective. -/
  kunnethMap_bijective : ∀ X Y, Function.Bijective (kunnethMap X Y)
  /-- Integration of an exterior product is the product of the integrations. -/
  integral_kunnethMap_tmul : ∀ {X Y d e} (hX : IsNonemptyEquidimensional X d)
      (hY : IsNonemptyEquidimensional Y e) (a : H X) (b : H Y),
    integral (product_isNonemptyEquidimensional hX hY)
        (kunnethMap X Y (a ⊗ₜ[F] b)) = integral hX a * integral hY b
  /-- Chow pushforward has the codimension shift prescribed by dimensions. -/
  cyclePushforward_mem : ∀ {X Y d e} (hX : IsNonemptyEquidimensional X d)
      (hY : IsNonemptyEquidimensional Y e) (f : X ⟶ Y) (i : ℤ)
      (alpha : CHgrade X i),
    cyclePushforward f alpha ∈ CHgrade Y (i + ((e : ℤ) - d))
  /-- Cycle classes commute with pullback. -/
  cycleClass_pullback : ∀ {X Y : V} (f : X ⟶ Y) (beta : CH Y),
    cycleClass X (cyclePullback f beta) = pullback f (cycleClass Y beta)
  /-- Cycle classes commute with pushforward. -/
  cycleClass_pushforward : ∀ {X Y d e} (hX : IsNonemptyEquidimensional X d)
      (hY : IsNonemptyEquidimensional Y e) (f : X ⟶ Y) (alpha : CH X),
    cycleClass Y (cyclePushforward f alpha) =
      pushforward hX hY f (cycleClass X alpha)
  /-- Cycle classes carry intersection products to cup products. -/
  cycleClass_mul : ∀ X (alpha beta : CH X),
    cycleClass X (alpha * beta) = cycleClass X alpha * cycleClass X beta
  /-- The point fundamental class has trace one. -/
  point_normalization :
    integral point_isNonemptyEquidimensional
      (cycleClass point (1 : CHgrade point 0)) = 1

namespace SchemeClassicalTheory

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
variable {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}

/-- Construct a scheme-valued theory with a supplied Tate-twist family. -/
def withTateTwist
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    (tateTwist : ∀ X i j,
      Hgrade X (i, j) ⊗[F] TateLine ≃ₗ[F] Hgrade X (i, j + 1)) :
    SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward :=
  { T with tateTwist := tateTwist }

/-- The `withTateTwist` constructor stores exactly its supplied equivalences. -/
theorem withTateTwist_tateTwist
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    (tateTwist : ∀ X i j,
      Hgrade X (i, j) ⊗[F] TateLine ≃ₗ[F] Hgrade X (i, j + 1)) :
    (withTateTwist T tateTwist).tateTwist = tateTwist := sorry

/-- The intrinsic predicate is equivalent to nonemptiness, equidimensionality, and the specified dimension. -/
theorem nonemptyEquidimensional_spec
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X : V} {d : ℕ} :
    T.IsNonemptyEquidimensional X d ↔
      Nonempty (T.scheme.obj X).left ∧ EquidimensionalSpace (T.scheme.obj X).left ∧
        dimension X = d := sorry

/-- The scheme presentation consists of faithful morphisms, smooth projectivity, and essential surjectivity. -/
theorem schemePresentation_spec
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward) :
    (∀ (X Y : V), Function.Bijective (T.scheme.map : (X ⟶ Y) → _)) ∧
    (∀ X, Smooth (T.scheme.obj X).hom) ∧
    (∀ X, Projective (T.scheme.obj X).hom) ∧
    (∀ S : SchemeOverField k, [Smooth S.hom] → [Projective S.hom] →
      ∃ X : V, Nonempty (T.scheme.obj X ≅ S)) := sorry

/-- Poincare duality comprises finite-dimensional graded pieces, the cup-trace pairing, and its perfectness. -/
theorem poincareDuality_spec
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward) :
    (∀ {X d}, T.IsNonemptyEquidimensional X d → ∀ p : ℤ × ℤ,
      Module.Finite F (Hgrade X p)) ∧
    (∀ {X d} (hX : T.IsNonemptyEquidimensional X d) (i j : ℤ)
      (a : Hgrade X (2 * (d : ℤ) - i, (d : ℤ) - j)) (b : Hgrade X (i, j)),
      T.poincarePairing hX i j a b = T.integral hX ((b : H X) * a)) ∧
    (∀ {X d} (hX : T.IsNonemptyEquidimensional X d) (i j : ℤ),
      Function.Bijective (T.poincarePairing hX i j)) := sorry

/-- The Kunneth formula describes pure tensors, grading, bijectivity, and integration. -/
theorem kunnethFormula_spec
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward) :
    (∀ X Y (a : H X) (b : H Y),
      T.kunnethMap X Y (a ⊗ₜ[F] b) =
        T.pullback (fst X Y) a * T.pullback (snd X Y) b) ∧
    (∀ X Y (p q : ℤ × ℤ) (a : Hgrade X p) (b : Hgrade Y q),
      T.kunnethMap X Y (a ⊗ₜ[F] b) ∈ Hgrade (product X Y) (p + q)) ∧
    (∀ X Y, Function.Bijective (T.kunnethMap X Y)) ∧
    (∀ {X Y d e} (hX : T.IsNonemptyEquidimensional X d)
      (hY : T.IsNonemptyEquidimensional Y e) (a : H X) (b : H Y),
      T.integral (T.product_isNonemptyEquidimensional hX hY)
          (T.kunnethMap X Y (a ⊗ₜ[F] b)) = T.integral hX a * T.integral hY b) := sorry

/-- Cycle-class compatibility comprises pullback, pushforward, products, and point normalization. -/
theorem cycleClassCompatibility_spec
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward) :
    (∀ {X Y : V} (f : X ⟶ Y) (beta : CH Y),
      T.cycleClass X (cyclePullback f beta) = T.pullback f (T.cycleClass Y beta)) ∧
    (∀ {X Y d e} (hX : T.IsNonemptyEquidimensional X d)
      (hY : T.IsNonemptyEquidimensional Y e) (f : X ⟶ Y) (alpha : CH X),
      T.cycleClass Y (cyclePushforward f alpha) =
        T.pushforward hX hY f (T.cycleClass X alpha)) ∧
    (∀ X (alpha beta : CH X),
      T.cycleClass X (alpha * beta) = T.cycleClass X alpha * T.cycleClass X beta) ∧
    T.integral T.point_isNonemptyEquidimensional
      (T.cycleClass point (1 : CHgrade point 0)) = 1 := sorry

end SchemeClassicalTheory

end WeilCohomology
