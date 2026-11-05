/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DirectSum.Module
public import ReasLib.AlgebraicGeometry.ChowCohomology
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative.Cycle
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward
public import ReasLib.AlgebraicGeometry.CycleGroup.Point
public import ReasLib.AlgebraicGeometry.Scheme.OverField.ClosedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.WeilCohomology.Trace
public import ReasLib.Topology.KrullDimension.Equidimensional
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.AlgebraicGeometry.WeilCohomology.Classical

@[expose] public section

noncomputable section

universe u v w x y z

namespace WeilCohomology

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct

/-- Comparisons with geometric Chow theory. The operational comparison covers all
codimensions, including schemes with components of different dimensions. The top
comparison supplies actual inverse data for zero cycles on equidimensional schemes;
its compatibility with cap product is a separate proposition below. -/
structure SchemeChowComparison
    (k : Type u) [Field k] {V : Type w} [Category.{z} V]
    (scheme : V ⥤ SchemeOverField k) (CH : V → Type y)
    [∀ X, CommRing (CH X)] (CHgrade : ∀ X, ℤ → Submodule ℤ (CH X))
    (IsNonemptyEquidimensional : V → ℕ → Prop)
    [∀ X, LocallyOfFiniteType (scheme.obj X).hom] where
  /-- Integral operational Chow cohomology, with its actual cap operations. -/
  operational : ∀ X i, CHgrade X i ≃+
    ChowCohomology.degree (fun _ ↦ 0) (scheme.obj X).hom i
  /-- Integral zero cycles modulo rational equivalence. -/
  top : ∀ {X d}, IsNonemptyEquidimensional X d →
    CHgrade X d ≃+ RelativeChow (fun _ ↦ 0) (scheme.obj X) 0

namespace SchemeChowComparison

/-- Evaluation of an operational class on the geometric fundamental cycle. -/
def capFundamental {k : Type u} [Field k]
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (d : ℕ) (i : ℤ)
    (a : ChowCohomology.degree (fun _ ↦ 0) X.hom i) :
    RelativeChow (fun _ ↦ 0) X ((d : ℤ) - i) :=
  a.cap (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom))
    CategoryTheory.IsPullback.of_id_snd d
    (RelativeChow.fundamentalClass (fun _ ↦ 0) X d)

/-- The genuine Chow class of a closed point, without a separability assumption. -/
def pointCycleClass {k : Type u} [Field k]
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : closedPoints X.left) : RelativeChow (fun _ ↦ 0) X 0 :=
  @chowClass X.left
    (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
      (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
        (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
    (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance 0
    (CycleGroup.point (X.hom.relativeDimensionFunction (fun _ ↦ 0)) 0 p
    (SchemeOverField.closedPoint_relativeDimensionFunction_eq_zero X p))

/-- Geometric compatibility of a Chow comparison. These laws concern the actual
intersection product, refined pullback and proper pushforward. They do not assume
any cohomological generation or separation conclusion. -/
structure RespectsOperations
    {k : Type u} [Field k] {V : Type w} [Category.{z} V]
    {scheme : V ⥤ SchemeOverField k} {CH : V → Type y}
    [∀ X, CommRing (CH X)] {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
    [∀ X, GradedAlgebra (CHgrade X)]
    {IsNonemptyEquidimensional : V → ℕ → Prop}
    [∀ X, LocallyOfFiniteType (scheme.obj X).hom]
    (C : SchemeChowComparison k scheme CH CHgrade IsNonemptyEquidimensional)
    (cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X)
    (cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y) : Prop where
  /-- The fundamental class corresponds to the operational unit. -/
  unit : ∀ X, C.operational X 0 1 = ChowCohomology.one (fun _ ↦ 0) (scheme.obj X).hom
  /-- Multiplication is the geometric intersection product. -/
  mul : ∀ X i j (a : CHgrade X i) (b : CHgrade X j),
    ((C.operational X (i + j)).symm
      (ChowCohomology.mul (fun _ ↦ 0) (scheme.obj X).hom
        (C.operational X i a) (C.operational X j b)) : CH X) = (a : CH X) * b
  /-- Refined pullback is restriction of operational Chow classes. -/
  pullback : ∀ {X Y : V} (f : X ⟶ Y) i (a : CHgrade Y i),
    ((C.operational X i).symm
      (BivariantClass.restrict (fun _ ↦ 0) (scheme.map f) (𝟙 _)
        (scheme.map f) CategoryTheory.IsPullback.of_id_snd i
        (C.operational Y i a)) : CH X) = cyclePullback f a
  /-- Proper pushforward is geometric pushforward after capping with fundamental
  cycles. The explicit homogeneous representative avoids choosing a grading proof. -/
  pushforward : ∀ {X Y d e}
      (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
      (f : X ⟶ Y) [IsProper (scheme.map f).left] i (a : CHgrade X i)
      (b : CHgrade Y (i + ((e : ℤ) - d))),
    (b : CH Y) = cyclePushforward f a →
      HEq (capFundamental (scheme.obj Y) e _ (C.operational Y _ b))
        (ChowGroup.map (fun _ ↦ 0) (scheme.obj X) (scheme.obj Y) (scheme.map f)
          ((d : ℤ) - i) (capFundamental (scheme.obj X) d i (C.operational X i a)))
  /-- The zero-cycle comparison is evaluation of the same operational comparison. -/
  top_cap : ∀ {X d} (hX : IsNonemptyEquidimensional X d) (a : CHgrade X d),
    C.top hX a = RelativeChow.castDegree (fun _ ↦ 0) (sub_self (d : ℤ))
      (capFundamental (scheme.obj X) d d (C.operational X d a))

end SchemeChowComparison

namespace SchemeClassicalTheory

/-- A fixed external Tate twist of a singly graded total space. -/
abbrev twistSlice := @Tate.Twist

/-- The exterior product on fixed external twists. -/
abbrev twistSliceTensorMap := @Tate.tensorMap

end SchemeClassicalTheory

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
    (Hgrade : ∀ X, ℤ → Submodule F (H X))
    (CHgrade : ∀ X, ℤ → Submodule ℤ (CH X))
    [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
    (cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X)
    (cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y) extends
      SmoothProjectivePresentation k V dimension product fst snd point CH CHgrade
        cyclePullback cyclePushforward where
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
  /-- A uniform comparison with actual integral geometric Chow groups. -/
  chowComparison :
    letI : ∀ X, LocallyOfFiniteType (scheme.obj X).hom :=
      fun X ↦ (projective X).isProper.toLocallyOfFiniteType
    SchemeChowComparison k scheme CH CHgrade IsNonemptyEquidimensional
  /-- The comparison preserves all geometric Chow operations. -/
  chow_compatible :
    letI : ∀ X, LocallyOfFiniteType (scheme.obj X).hom :=
      fun X ↦ (projective X).isProper.toLocallyOfFiniteType
    chowComparison.RespectsOperations cyclePullback cyclePushforward
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
  /-- The specified class is the class of this particular geometric closed point,
  including points with inseparable residue fields. -/
  closedPointClass_comparison :
    letI : ∀ X, LocallyOfFiniteType (scheme.obj X).hom :=
      fun X ↦ (projective X).isProper.toLocallyOfFiniteType
    ∀ {X d} (hX : IsNonemptyEquidimensional X d)
      (p : closedPoints (scheme.obj X).left),
      chowComparison.top hX (closedPointClass hX p) =
        SchemeChowComparison.pointCycleClass (scheme.obj X) p
  /-- The chosen Tate line has dimension one. -/
  tateLine_rank : Module.finrank F TateLine = 1
  /-- The singly graded cohomology summands exhaust total cohomology. -/
  Hgrade_isInternal : ∀ X, DirectSum.IsInternal (Hgrade X)
  /-- Contravariant pullback on singly graded cohomology. -/
  pullback : ∀ {X Y : V}, (X ⟶ Y) → Hgrade Y →ₐᵍ[F] Hgrade X
  /-- Pullback by an identity morphism is the identity. -/
  pullback_id : ∀ X, pullback (𝟙 X) = GradedAlgHom.id F (Hgrade X)
  /-- Pullback reverses composition. -/
  pullback_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
    pullback (f ≫ g) = (pullback f).comp (pullback g)
  /-- Homogeneous cup products satisfy graded commutativity in cohomological degree. -/
  gradedComm : ∀ X {i i' : ℤ} (a : Hgrade X (i))
      (b : Hgrade X (i')),
    (a : H X) * b = (-1 : H X) ^ (i * i').natAbs * ((b : H X) * a)
  /-- The additive cycle-class map on total Chow and cohomology groups. -/
  cycleClass : ∀ X, CH X →+ H X
  /-- A codimension-i cycle has cohomological degree 2i in Tate coordinates.
  Its externally twisted class is exposed by twistedCycleClass. -/
  cycleClass_mem : ∀ X (i : ℤ) (alpha : CHgrade X i),
    cycleClass X alpha ∈ Hgrade X (2 * i)
  /-- The trace on a nonempty equidimensional scheme. -/
  integral : ∀ {X d}, IsNonemptyEquidimensional X d → H X →ₗ[F] F
  /-- The trace vanishes away from top cohomological degree. -/
  integral_vanishes : ∀ {X d} (hX : IsNonemptyEquidimensional X d)
      (p : ℤ), p ≠ (2 * (d : ℤ)) →
    ∀ a : Hgrade X p, integral hX a = 0
  /-- Every homogeneous cohomology group is finite-dimensional. -/
  finiteDimensional : ∀ {X d}, IsNonemptyEquidimensional X d →
    ∀ p : ℤ, Module.Finite F (Hgrade X p)
  /-- The linear map associated to the Poincare pairing. -/
  poincarePairing : ∀ {X d} (hX : IsNonemptyEquidimensional X d) (i : ℤ),
    Hgrade X (2 * (d : ℤ) - i) →ₗ[F]
      (Hgrade X (i) →ₗ[F] F)
  /-- The Poincare pairing is cup product followed by the trace. -/
  poincarePairing_apply : ∀ {X d} (hX : IsNonemptyEquidimensional X d) (i : ℤ)
      (a : Hgrade X (2 * (d : ℤ) - i))
      (b : Hgrade X (i)),
    poincarePairing hX i a b = integral hX ((b : H X) * a)
  /-- The Poincare pairing is perfect in every cohomological degree. -/
  poincarePairing_bijective : ∀ {X d} (hX : IsNonemptyEquidimensional X d)
      (i : ℤ), Function.Bijective (poincarePairing hX i)
  /-- Cohomological pushforward between nonempty equidimensional schemes. -/
  pushforward : ∀ {X Y d e}, IsNonemptyEquidimensional X d →
    IsNonemptyEquidimensional Y e → (X ⟶ Y) → H X →ₗ[F] H Y
  /-- Pushforward has the cohomological degree shift prescribed by dimensions. -/
  pushforward_mem : ∀ {X Y d e} (hX : IsNonemptyEquidimensional X d)
      (hY : IsNonemptyEquidimensional Y e) (f : X ⟶ Y) (i : ℤ)
      (a : Hgrade X (i)),
    pushforward hX hY f a ∈
      Hgrade Y (i + 2 * ((e : ℤ) - d))
  /-- Pushforward is adjoint to pullback for the Poincare pairings. -/
  pushforward_spec : ∀ {X Y d e} (hX : IsNonemptyEquidimensional X d)
      (hY : IsNonemptyEquidimensional Y e) (f : X ⟶ Y) (a : H X) (b : H Y),
    integral hX (pullback f b * a) = integral hY (b * pushforward hX hY f a)
  /-- The exterior-product map in the Kunneth formula. -/
  kunnethMap : ∀ X Y, H X ⊗[F] H Y →ₗ[F] H (product X Y)
  /-- On pure tensors, the Kunneth map is the product of pullbacks. -/
  kunnethMap_tmul : ∀ X Y (a : H X) (b : H Y),
    kunnethMap X Y (a ⊗ₜ[F] b) = pullback (fst X Y) a * pullback (snd X Y) b
  /-- The Kunneth map adds cohomological degrees. -/
  kunnethMap_mem : ∀ X Y (p q : ℤ) (a : Hgrade X p) (b : Hgrade Y q),
    kunnethMap X Y (a ⊗ₜ[F] b) ∈ Hgrade (product X Y) (p + q)
  /-- Exterior product is an isomorphism on any specified external twists. -/
  kunnethMap_fixedTwists : ∀ X Y (r s : ℤ),
    Function.Bijective (Tate.tensorMap tateLine_rank (kunnethMap X Y) r s)
  /-- Integration of an exterior product of top-bidegree classes is multiplicative. -/
  integral_kunnethMap_tmul : ∀ {X Y d e} (hX : IsNonemptyEquidimensional X d)
      (hY : IsNonemptyEquidimensional Y e)
      (a : Hgrade X (2 * (d : ℤ)))
      (b : Hgrade Y (2 * (e : ℤ))),
    integral (product_isNonemptyEquidimensional hX hY)
        (kunnethMap X Y ((a : H X) ⊗ₜ[F] (b : H Y))) = integral hX a * integral hY b
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
variable {Hgrade : ∀ X, ℤ → Submodule F (H X)}
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
variable [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}


/- Source-compatible names for the inherited presentation projections.
The stored data and laws belong only to `SmoothProjectivePresentation`. -/
namespace PresentationProjection

variable (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
  H CH Hgrade CHgrade cyclePullback cyclePushforward)

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

section GeometricChow

variable (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
  H CH Hgrade CHgrade cyclePullback cyclePushforward)

local instance chowFiniteType (X : V) : LocallyOfFiniteType (T.scheme.obj X).hom :=
  (T.projective X).isProper.toLocallyOfFiniteType

/-- The uniform top Chow comparison supplied by the theory. -/
abbrev chowTopEquiv {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) :
    CHgrade X d ≃+ RelativeChow (fun _ ↦ 0) (T.scheme.obj X) 0 :=
  T.chowComparison.top hX

/-- The closed-point field is determined by its genuine geometric point cycle. -/
theorem closedPointClass_eq_geometric {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d)
    (p : closedPoints (T.scheme.obj X).left) :
    T.closedPointClass hX p = (T.chowTopEquiv hX).symm
      (SchemeChowComparison.pointCycleClass (T.scheme.obj X) p) :=
  (T.chowTopEquiv hX).injective (by
    rw [T.closedPointClass_comparison, AddEquiv.apply_symm_apply])

end GeometricChow

section ExternalTwists

variable (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
  H CH Hgrade CHgrade cyclePullback cyclePushforward)

/-- External Tate twists of the singly graded total cohomology. -/
abbrev twistedCohomology (_T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward) (X : V) (n : ℤ) := Tate.Twist F TateLine (H X) n

/-- A homogeneous degree with an external Tate twist. There is no inclusion of
all twists as independent summands of H X. -/
abbrev twistedGrade
    (_T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward) (X : V) (i n : ℤ) := Tate.Twist F TateLine (Hgrade X i) n

/-- The Tate shift is derived from genuine tensor powers, not stored as an
identification between subspaces of H X. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def tateTwist (X : V) (i n : ℤ) :
    T.twistedGrade X i n ⊗[F] TateLine ≃ₗ[F] T.twistedGrade X i (n + 1) :=
  Tate.shift T.tateLine_rank (Hgrade X i) n

/-- The degreewise cycle class with its source-prescribed external Tate twist. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def twistedCycleClass (X : V) (i : ℤ) : CHgrade X i →+ T.twistedGrade X (2 * i) i :=
  (Tate.trivialization T.tateLine_rank (Hgrade X (2 * i)) i).symm.toLinearMap.toAddMonoidHom.comp
    { toFun := fun z ↦ ⟨T.cycleClass X z, T.cycleClass_mem X i z⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b ↦ Subtype.ext ((T.cycleClass X).map_add a b) }

/-- Pullback acts on a fixed external twist. -/
def twistedPullback {X Y : V} (f : X ⟶ Y) (n : ℤ) :
    T.twistedCohomology Y n →ₗ[F] T.twistedCohomology X n :=
  TensorProduct.map (T.pullback f).toAlgHom.toLinearMap LinearMap.id

/-- A chosen trace on an external twist; the field `integral` contains its
coordinate functional with respect to the genuine Tate-line coordinate. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def twistedIntegral
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) :
    T.twistedCohomology X d →ₗ[F] F :=
  (T.integral hX).comp (Tate.trivialization T.tateLine_rank (H X) d).toLinearMap

/-- Pushforward on dimension twists, obtained by transporting the actual coordinate map. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def twistedPushforward
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X Y : V} {d e : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y e) (f : X ⟶ Y) :
    T.twistedCohomology X d →ₗ[F] T.twistedCohomology Y e :=
  Tate.map T.tateLine_rank (T.pushforward hX hY f) d e

/-- Exterior product on genuine fixed external twists. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def twistedKunnethMap
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    (X Y : V) (r s : ℤ) :
    T.twistedCohomology X r ⊗[F] T.twistedCohomology Y s →ₗ[F]
      T.twistedCohomology (product X Y) (r + s) :=
  Tate.tensorMap T.tateLine_rank (T.kunnethMap X Y) r s

/-- Poincare pairing on external twists n and d-n, reconstructed from its
actual cup-trace coordinate map. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def twistedPoincarePairing
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) (i n : ℤ) :
    T.twistedGrade X (2 * (d : ℤ) - i) ((d : ℤ) - n) →ₗ[F]
      (T.twistedGrade X i n →ₗ[F] F) :=
  (T.poincarePairing hX i).compl₁₂
    (Tate.trivialization T.tateLine_rank (Hgrade X (2 * (d : ℤ) - i))
      ((d : ℤ) - n)).toLinearMap
    (Tate.trivialization T.tateLine_rank (Hgrade X i) n).toLinearMap

end ExternalTwists

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
    (∀ {X d}, T.IsNonemptyEquidimensional X d → ∀ p : ℤ,
      Module.Finite F (Hgrade X p)) ∧
    (∀ {X d} (hX : T.IsNonemptyEquidimensional X d) (i : ℤ)
      (a : Hgrade X (2 * (d : ℤ) - i)) (b : Hgrade X (i)),
      T.poincarePairing hX i a b = T.integral hX ((b : H X) * a)) ∧
    (∀ {X d} (hX : T.IsNonemptyEquidimensional X d) (i : ℤ),
      Function.Bijective (T.poincarePairing hX i)) := sorry

/-- The Kunneth formula describes pure tensors, grading, fixed-twist isomorphisms,
and integration of top-bidegree exterior products. -/
theorem kunnethFormula_spec
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward) :
    (∀ X Y (a : H X) (b : H Y),
      T.kunnethMap X Y (a ⊗ₜ[F] b) =
        T.pullback (fst X Y) a * T.pullback (snd X Y) b) ∧
    (∀ X Y (p q : ℤ) (a : Hgrade X p) (b : Hgrade Y q),
      T.kunnethMap X Y (a ⊗ₜ[F] b) ∈ Hgrade (product X Y) (p + q)) ∧
    (∀ X Y (r s : ℤ),
      Function.Bijective (Tate.tensorMap T.tateLine_rank (T.kunnethMap X Y) r s)) ∧
    (∀ {X Y d e} (hX : T.IsNonemptyEquidimensional X d)
      (hY : T.IsNonemptyEquidimensional Y e)
      (a : Hgrade X (2 * (d : ℤ)))
      (b : Hgrade Y (2 * (e : ℤ))),
      T.integral (T.product_isNonemptyEquidimensional hX hY)
          (T.kunnethMap X Y ((a : H X) ⊗ₜ[F] (b : H Y))) =
        T.integral hX a * T.integral hY b) := sorry

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
