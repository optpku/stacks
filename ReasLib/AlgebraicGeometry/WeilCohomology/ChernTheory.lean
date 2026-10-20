/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChernClass.Theory
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback
public import ReasLib.AlgebraicGeometry.WeilCohomology.CycleClass.ClosedSubscheme
public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.AxiomA8

@[expose] public section

noncomputable section

universe u v w x y z q

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators TensorProduct

namespace WeilCohomology

/-- Raw data (D0), (D1), and (D2') on an existing presentation of all smooth
projective schemes. The surrounding geometry and integral Chow theory belong to
`SmoothProjectiveContext`, rather than being freely chosen cohomology data. -/
structure ChernTheory
    {k : Type u} [Field k] (F : Type v) [Field F] [CharZero F]
    (TateLine : Type x) [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    (geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle)
    (H : V → Type q) [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] where
  /-- Data (D0): the Tate line is one-dimensional. -/
  tateLine_rank : Module.finrank F TateLine = 1
  /-- The cohomological-degree and Tate-twist summands of total cohomology. -/
  Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X)
  /-- The bigraded summands exhaust total cohomology. -/
  Hgrade_isInternal : ∀ X, DirectSum.IsInternal (Hgrade X)
  /-- Tensoring with the Tate line raises the twist index by one. -/
  tateTwist : ∀ X i j, Hgrade X (i, j) ⊗[F] TateLine ≃ₗ[F] Hgrade X (i, j + 1)
  /-- The unit has bidegree `(0, 0)`. -/
  one_mem : ∀ X, (1 : H X) ∈ Hgrade X (0, 0)
  /-- Cup product adds both bidegrees. -/
  mul_mem : ∀ X {p r : ℤ × ℤ} (a : Hgrade X p) (b : Hgrade X r),
    (a : H X) * b ∈ Hgrade X (p + r)
  /-- Homogeneous cup products are graded-commutative. -/
  gradedComm : ∀ X {i i' j j' : ℤ} (a : Hgrade X (i, j))
      (b : Hgrade X (i', j')),
    (a : H X) * b = (-1 : H X) ^ (i * i').natAbs * ((b : H X) * a)
  /-- Data (D1): contravariant pullback on total cohomology. -/
  pullback : ∀ {X Y : V}, (X ⟶ Y) → H Y →ₐ[F] H X
  /-- Pullback preserves both bidegrees. -/
  pullback_mem : ∀ {X Y : V} (f : X ⟶ Y) (p : ℤ × ℤ) (a : Hgrade Y p),
    pullback f a ∈ Hgrade X p
  /-- Pullback by an identity is the identity. -/
  pullback_id : ∀ X, pullback (𝟙 X) = AlgHom.id F (H X)
  /-- Pullback reverses composition. -/
  pullback_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
    pullback (f ≫ g) = (pullback f).comp (pullback g)
  /-- Data (D2'): the first Chern class on the canonical Picard group. -/
  firstChernClass : ∀ X,
    (geometry.scheme.obj X).left.PicardGroup →+ Hgrade X (2, 1)

namespace ChernTheory

/-- Forget the axioms and auxiliary geometric choices of an existing pre-Weil
theory, after identifying its Picard groups with the canonical Picard groups of
the smooth-projective context. -/
def ofPreWeilTheory
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{w} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type x} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H Picard Cycle : V → Type x}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine V H Picard Cycle)
    (picardEquiv : ∀ X, (geometry.scheme.obj X).left.PicardGroup ≃+ Picard X) :
    ChernTheory F TateLine geometry H where
  tateLine_rank := T.tateLine_rank
  Hgrade := T.Hgrade
  Hgrade_isInternal := T.Hgrade_isInternal
  tateTwist := T.tateTwist
  one_mem := T.one_mem
  mul_mem := T.mul_mem
  gradedComm := T.gradedComm
  pullback := T.pullback
  pullback_mem := T.pullback_mem
  pullback_id := T.pullback_id
  pullback_comp := T.pullback_comp
  firstChernClass := fun X ↦ (T.firstChernClass X).comp (picardEquiv X).toAddMonoidHom

/-- Build raw D0/D1/D2' data from its Tate line, grading, contravariant
cohomology functor, and canonical-Picard first Chern class. -/
def ofFunctor := @ChernTheory.mk

/-- `ofFunctor` retains the supplied bigrading. -/
theorem ofFunctor_Hgrade
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    (tateLine_rank : Module.finrank F TateLine = 1)
    (Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X))
    (Hgrade_isInternal : ∀ X, DirectSum.IsInternal (Hgrade X))
    (tateTwist : ∀ X i j, Hgrade X (i, j) ⊗[F] TateLine ≃ₗ[F] Hgrade X (i, j + 1))
    (one_mem : ∀ X, (1 : H X) ∈ Hgrade X (0, 0))
    (mul_mem : ∀ X {p r : ℤ × ℤ} (a : Hgrade X p) (b : Hgrade X r),
      (a : H X) * b ∈ Hgrade X (p + r))
    (gradedComm : ∀ X {i i' j j' : ℤ} (a : Hgrade X (i, j))
      (b : Hgrade X (i', j')),
      (a : H X) * b = (-1 : H X) ^ (i * i').natAbs * ((b : H X) * a))
    (pullback : ∀ {X Y : V}, (X ⟶ Y) → H Y →ₐ[F] H X)
    (pullback_mem : ∀ {X Y : V} (f : X ⟶ Y) (p : ℤ × ℤ) (a : Hgrade Y p),
      pullback f a ∈ Hgrade X p)
    (pullback_id : ∀ X, pullback (𝟙 X) = AlgHom.id F (H X))
    (pullback_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
      pullback (f ≫ g) = (pullback f).comp (pullback g))
    (firstChernClass : ∀ X,
      (geometry.scheme.obj X).left.PicardGroup →+ Hgrade X (2, 1)) :
    (ofFunctor tateLine_rank Hgrade Hgrade_isInternal tateTwist one_mem mul_mem
      gradedComm pullback pullback_mem pullback_id pullback_comp firstChernClass).Hgrade =
        Hgrade := sorry

/-- Pullback restricted to a fixed bidegree. -/
noncomputable def pullbackGrade
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    (T : ChernTheory F TateLine geometry H) {X Y : V}
    (f : X ⟶ Y) (p : ℤ × ℤ) : T.Hgrade Y p →ₗ[F] T.Hgrade X p :=
  LinearMap.codRestrict (T.Hgrade X p)
    ((T.pullback f).toLinearMap.domRestrict (T.Hgrade Y p)) (T.pullback_mem f p)

/-- Restricted pullback agrees with total pullback. -/
theorem pullbackGrade_apply
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    (T : ChernTheory F TateLine geometry H) {X Y : V}
    (f : X ⟶ Y) (p : ℤ × ℤ) (a : T.Hgrade Y p) :
    T.pullback f a = T.pullbackGrade f p a := sorry

/-- The canonical exterior-product map determined by D1 and the product in the
smooth-projective context. -/
noncomputable def kunnethMap
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    (T : ChernTheory F TateLine geometry H) (X Y : V) :
    H X ⊗[F] H Y →ₗ[F] H (product X Y) :=
  TensorProduct.lift ((LinearMap.mul F (H (product X Y))).compl₁₂
    (T.pullback (fst X Y)).toLinearMap (T.pullback (snd X Y)).toLinearMap)

/-- The Künneth map sends a pure tensor to the cup product of the two pullbacks. -/
theorem kunnethMap_tmul
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    (T : ChernTheory F TateLine geometry H) (X Y : V) (a : H X) (b : H Y) :
    T.kunnethMap X Y (a ⊗ₜ[F] b) =
      T.pullback (fst X Y) a * T.pullback (snd X Y) b := sorry

/-- A cycle-class system on the canonical Chow rings of the smooth-projective context. -/
structure CycleClass
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    (T : ChernTheory F TateLine geometry H) where
  /-- The cycle-class ring homomorphism. -/
  map : ∀ X, CH X →+* H X
  /-- Codimension `i` maps to bidegree `(2 * i, i)`. -/
  map_mem : ∀ X (i : ℤ) (z : CHgrade X i), map X z ∈ T.Hgrade X (2 * i, i)
  /-- Cycle classes commute with canonical Chow pullback. -/
  map_pullback : ∀ {X Y : V} (f : X ⟶ Y) (z : CH Y),
    map X (cyclePullback f z) = T.pullback f (map Y z)
  /-- The canonical cycle of an effective Cartier divisor maps to its first Chern class. -/
  map_cartier : ∀ {Y X : V} (i : Y ⟶ X)
      (hi : IsEffectiveCartierDivisor (geometry.scheme.map i).left)
      (z : CHgrade X 1),
    (z : CH X) = cyclePushforward i (1 : CHgrade Y 0) →
      map X z = T.firstChernClass X
        (effectiveCartierDivisorPicardClass (geometry.scheme.map i).left hi)

namespace CycleClass

/-- Build a cycle-class system from explicit homomorphisms and their canonical
Chow compatibility laws. -/
def ofHom := @CycleClass.mk

/-- The map of a cycle-class system built by `ofHom` is the supplied map. -/
theorem ofHom_map
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    {T : ChernTheory F TateLine geometry H}
    (map : ∀ X, CH X →+* H X)
    (map_mem : ∀ X (i : ℤ) (z : CHgrade X i), map X z ∈ T.Hgrade X (2 * i, i))
    (map_pullback : ∀ {X Y : V} (f : X ⟶ Y) (z : CH Y),
      map X (cyclePullback f z) = T.pullback f (map Y z))
    (map_cartier : ∀ {Y X : V} (i : Y ⟶ X)
      (hi : IsEffectiveCartierDivisor (geometry.scheme.map i).left)
      (z : CHgrade X 1),
      (z : CH X) = cyclePushforward i (1 : CHgrade Y 0) →
        map X z = T.firstChernClass X
          (effectiveCartierDivisorPicardClass (geometry.scheme.map i).left hi)) :
    (ofHom map map_mem map_pullback map_cartier).map = map := sorry

end CycleClass

/-- A morphism is the diagonal for the product supplied by the smooth-projective context. -/
def IsDiagonal
    {k : Type u} [Field k] {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    (geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle)
    {X : V} (diagonal : X ⟶ product X X) : Prop :=
  geometry.scheme.map diagonal ≫ (geometry.schemeProduct X X).hom =
    Limits.prod.lift (𝟙 _) (𝟙 _)

/-- `IsDiagonal` is the canonical product-diagonal equation. -/
theorem isDiagonal_iff
    {k : Type u} [Field k] {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    (geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle)
    {X : V} (diagonal : X ⟶ product X X) :
    IsDiagonal geometry diagonal ↔
      geometry.scheme.map diagonal ≫ (geometry.schemeProduct X X).hom =
        Limits.prod.lift (𝟙 _) (𝟙 _) := sorry

/-- A homogeneous Chow class is the canonical pushforward of the fundamental
class along a represented diagonal. -/
def IsDiagonalCycle
    {V : Type w} [Category.{z} V] {product : V → V → V}
    {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    (cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y)
    {X : V} (d : ℕ) (diagonal : X ⟶ product X X)
    (z : CHgrade (product X X) d) : Prop :=
  (z : CH (product X X)) = cyclePushforward diagonal (1 : CHgrade X 0)

/-- `IsDiagonalCycle` unfolds to canonical Chow pushforward along the diagonal. -/
theorem isDiagonalCycle_iff
    {V : Type w} [Category.{z} V] {product : V → V → V}
    {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    (cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y)
    {X : V} (d : ℕ) (diagonal : X ⟶ product X X)
    (z : CHgrade (product X X) d) :
    IsDiagonalCycle cyclePushforward d diagonal z ↔
      (z : CH (product X X)) = cyclePushforward diagonal (1 : CHgrade X 0) := sorry

/-- A trace normalized by the canonical Chow diagonal and vanishing away from
the top bidegree. -/
def IsNormalizedTrace
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    (T : ChernTheory F TateLine geometry H) (gamma : T.CycleClass)
    (X : V) (trace : H X →ₗ[F] F) : Prop :=
  (∀ p : ℤ × ℤ, p ≠ (2 * (dimension X : ℤ), (dimension X : ℤ)) →
      ∀ a : T.Hgrade X p, trace a = 0) ∧
    ∀ (diagonal : X ⟶ product X X), IsDiagonal geometry diagonal →
      ∀ (z : CHgrade (product X X) (dimension X)),
        IsDiagonalCycle cyclePushforward (dimension X) diagonal z →
          ∃ diagonalTensor : H X ⊗[F] H X,
            T.kunnethMap X X diagonalTensor = gamma.map (product X X) z ∧
              contractRight trace diagonalTensor = 1

/-- The normalized-trace predicate is its top-degree vanishing and canonical
diagonal-contraction formula. -/
theorem isNormalizedTrace_iff
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    (T : ChernTheory F TateLine geometry H) (gamma : T.CycleClass)
    (X : V) (trace : H X →ₗ[F] F) :
    T.IsNormalizedTrace gamma X trace ↔
      ((∀ p : ℤ × ℤ, p ≠ (2 * (dimension X : ℤ), (dimension X : ℤ)) →
          ∀ a : T.Hgrade X p, trace a = 0) ∧
        ∀ (diagonal : X ⟶ product X X), IsDiagonal geometry diagonal →
          ∀ (z : CHgrade (product X X) (dimension X)),
            IsDiagonalCycle cyclePushforward (dimension X) diagonal z →
              ∃ diagonalTensor : H X ⊗[F] H X,
                T.kunnethMap X X diagonalTensor = gamma.map (product X X) z ∧
                  contractRight trace diagonalTensor = 1) := sorry

/-- The first four axioms for raw D0/D1/D2' data, stated using the canonical
scheme, Picard, and divisor geometry of the smooth-projective context. -/
structure InitialAxioms
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    (T : ChernTheory F TateLine geometry H) : Prop where
  /-- Axiom (A1): empty objects vanish, and complementary clopen restrictions
  identify cohomology with a product. -/
  axiomA1 :
    (∀ X, IsEmpty (geometry.scheme.obj X).left → ∀ a : H X, a = 0) ∧
      ∀ (X : V) (U : (geometry.scheme.obj X).left.Opens)
        (hU : IsClopen (U : Set (geometry.scheme.obj X).left))
        (XU XU' : V) (iU : XU ⟶ X) (iU' : XU' ⟶ X)
        (eU : (geometry.scheme.obj XU).left ≅ U.toScheme)
        (eU' : (geometry.scheme.obj XU').left ≅
          (ChernClass.clopenComplement U hU).toScheme),
        (geometry.scheme.map iU).left = eU.hom ≫ U.ι →
          (geometry.scheme.map iU').left = eU'.hom ≫
            (ChernClass.clopenComplement U hU).ι →
          Function.Bijective (fun a : H X ↦ (T.pullback iU a, T.pullback iU' a))
  /-- Axiom (A2): first Chern classes commute with canonical Picard pullback. -/
  axiomA2 : ∀ {X Y : V} (f : X ⟶ Y)
      (L : (geometry.scheme.obj Y).left.PicardGroup),
    T.pullback f (T.firstChernClass Y L) =
      T.firstChernClass X (Scheme.Hom.picardPullback (geometry.scheme.map f).left L)
  /-- Axiom (A3): the canonical projective-bundle formula is an isomorphism in
  every bidegree. -/
  axiomA3 : ∀ {P X : V} (p : P ⟶ X) (E : (geometry.scheme.obj X).left.Modules)
      (n : ℕ) (hE : Scheme.Modules.IsFiniteLocallyFreeOfRank n E)
      (hp : Scheme.ProjectiveBundle.Representation (geometry.scheme.map p).left E)
      (i j : ℤ),
    ∃ e : (∀ r : Fin n,
        T.Hgrade X (i - 2 * ((r : ℕ) : ℤ), j - ((r : ℕ) : ℤ))) ≃ₗ[F]
          T.Hgrade P (i, j),
      ∀ a, (e a : H P) = ∑ r : Fin n,
        T.pullback p (a r) *
          (T.firstChernClass P
            (ChernClass.tautologicalPicardClass (geometry.scheme.map p).left E hp) : H P) ^
              (r : ℕ)
  /-- Axiom (A4): a class vanishing on an effective Cartier divisor is
  annihilated by the divisor's canonical first Chern class. -/
  axiomA4 : ∀ {Y X : V} (i : Y ⟶ X)
      (hi : IsEffectiveCartierDivisor (geometry.scheme.map i).left) (a : H X),
    T.pullback i a = 0 →
      a * T.firstChernClass X
        (effectiveCartierDivisorPicardClass (geometry.scheme.map i).left hi) = 0

namespace InitialAxioms

/-- Construct the first-four-axiom bundle from its four component conditions. -/
def ofFields := @InitialAxioms.mk

end InitialAxioms

/-- Axioms (A1)--(A4) determine a unique cycle-class map on the canonical Chow
rings; this is the interface supplied by `existsUniqueCycleClass`. -/
theorem existsUniqueCycleClass
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    (T : ChernTheory F TateLine geometry H) (h : T.InitialAxioms) :
    ∃ gamma : T.CycleClass, ∀ gamma' : T.CycleClass, gamma' = gamma := sorry

/-- Axiom (A8) using an object that represents the canonical spectrum of global
sections and the canonical map to it. -/
def SatisfiesAxiomA8
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    (T : ChernTheory F TateLine geometry H) : Prop :=
  ∀ (X G : V) (g : X ⟶ G)
    (eG : geometry.scheme.obj G ≅ SchemeOverField.globalSectionsSpec (geometry.scheme.obj X)),
    (geometry.scheme.map g).left =
        (SchemeOverField.toGlobalSectionsSpec (geometry.scheme.obj X)).left ≫ eG.inv.left →
      Function.Bijective (T.pullbackGrade g (0, 0))

/-- The A8 predicate unfolds to pullback along the canonical global-sections map. -/
theorem satisfiesAxiomA8_iff
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    (T : ChernTheory F TateLine geometry H) :
    T.SatisfiesAxiomA8 ↔
      ∀ (X G : V) (g : X ⟶ G)
        (eG : geometry.scheme.obj G ≅ SchemeOverField.globalSectionsSpec (geometry.scheme.obj X)),
        (geometry.scheme.map g).left =
            (SchemeOverField.toGlobalSectionsSpec (geometry.scheme.obj X)).left ≫ eG.inv.left →
          Function.Bijective (T.pullbackGrade g (0, 0)) := sorry

/-- Axiom (A9): normalized traces obey the divisor trace formula. -/
def SatisfiesAxiomA9
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    (T : ChernTheory F TateLine geometry H) : Prop :=
  ∀ {Y X : V} (i : Y ⟶ X)
    (hi : IsEffectiveCartierDivisor (geometry.scheme.map i).left),
    Nonempty (geometry.scheme.obj X).left → EquidimensionalSpace (geometry.scheme.obj X).left →
      Nonempty (geometry.scheme.obj Y).left → EquidimensionalSpace (geometry.scheme.obj Y).left →
      dimension X = dimension Y + 1 →
        ∀ (gamma : T.CycleClass) (traceX : H X →ₗ[F] F) (traceY : H Y →ₗ[F] F),
          T.IsNormalizedTrace gamma X traceX → T.IsNormalizedTrace gamma Y traceY →
            ∀ a : T.Hgrade X (2 * (dimension Y : ℤ), (dimension Y : ℤ)),
              traceY (T.pullback i a) = traceX
                ((a : H X) * T.firstChernClass X
                  (effectiveCartierDivisorPicardClass (geometry.scheme.map i).left hi))

/-- The A9 predicate unfolds to the canonical divisor trace formula. -/
theorem satisfiesAxiomA9_iff
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    (T : ChernTheory F TateLine geometry H) :
    T.SatisfiesAxiomA9 ↔
      ∀ {Y X : V} (i : Y ⟶ X)
        (hi : IsEffectiveCartierDivisor (geometry.scheme.map i).left),
        Nonempty (geometry.scheme.obj X).left →
          EquidimensionalSpace (geometry.scheme.obj X).left →
          Nonempty (geometry.scheme.obj Y).left →
          EquidimensionalSpace (geometry.scheme.obj Y).left →
          dimension X = dimension Y + 1 →
            ∀ (gamma : T.CycleClass) (traceX : H X →ₗ[F] F) (traceY : H Y →ₗ[F] F),
              T.IsNormalizedTrace gamma X traceX →
                T.IsNormalizedTrace gamma Y traceY →
                ∀ a : T.Hgrade X (2 * (dimension Y : ℤ), (dimension Y : ℤ)),
                  traceY (T.pullback i a) = traceX
                    ((a : H X) * T.firstChernClass X
                      (effectiveCartierDivisorPicardClass
                        (geometry.scheme.map i).left hi)) := sorry

/-- Axioms (A1)--(A9) for fixed D0/D1/D2' data on the canonical
smooth-projective geometry. -/
structure Axioms
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    (T : ChernTheory F TateLine geometry H) : Prop extends InitialAxioms T where
  /-- Axiom (A5): point cohomology is `F`, and the canonical Künneth maps are isomorphisms. -/
  axiomA5 :
    Function.Bijective (algebraMap F (H point)) ∧
      ∀ X Y, Function.Bijective (T.kunnethMap X Y)
  /-- Axiom (A6): every nonempty equidimensional object admits a normalized trace
  for the cycle class canonically determined by (A1)--(A4). -/
  axiomA6 : ∃ gamma : T.CycleClass, ∀ X,
    Nonempty (geometry.scheme.obj X).left → EquidimensionalSpace (geometry.scheme.obj X).left →
      ∃ trace : H X →ₗ[F] F, T.IsNormalizedTrace gamma X trace
  /-- Axiom (A7): pullback by a represented blowup in a smooth center is injective. -/
  axiomA7 : ∀ {X' X : V} (b : X' ⟶ X) (I : (geometry.scheme.obj X).left.IdealSheafData),
    Smooth (I.subschemeι ≫ (geometry.scheme.obj X).hom) →
      IsBlowup (geometry.scheme.map b).left I → Function.Injective (T.pullback b)
  /-- Axiom (A8): degree-zero pullback along the canonical global-sections map is bijective. -/
  axiomA8 : T.SatisfiesAxiomA8
  /-- Axiom (A9): normalized traces satisfy the effective-divisor trace formula. -/
  axiomA9 : T.SatisfiesAxiomA9

namespace Axioms

/-- Assemble the full axiom bundle from the first four axioms and the remaining
five axioms. -/
def ofInitialAxioms
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    {T : ChernTheory F TateLine geometry H}
    (initial : T.InitialAxioms)
    (axiomA5 : Function.Bijective (algebraMap F (H point)) ∧
      ∀ X Y, Function.Bijective (T.kunnethMap X Y))
    (axiomA6 : ∃ gamma : T.CycleClass, ∀ X,
      Nonempty (geometry.scheme.obj X).left →
        EquidimensionalSpace (geometry.scheme.obj X).left →
        ∃ trace : H X →ₗ[F] F, T.IsNormalizedTrace gamma X trace)
    (axiomA7 : ∀ {X' X : V} (b : X' ⟶ X)
      (I : (geometry.scheme.obj X).left.IdealSheafData),
      Smooth (I.subschemeι ≫ (geometry.scheme.obj X).hom) →
        IsBlowup (geometry.scheme.map b).left I → Function.Injective (T.pullback b))
    (axiomA8 : T.SatisfiesAxiomA8) (axiomA9 : T.SatisfiesAxiomA9) : T.Axioms where
  toInitialAxioms := initial
  axiomA5 := axiomA5
  axiomA6 := axiomA6
  axiomA7 := axiomA7
  axiomA8 := axiomA8
  axiomA9 := axiomA9

/-- Forget an existing pre-Weil theory to raw D0/D1/D2' data and assemble its
axioms using the canonical smooth-projective geometry. -/
def ofPreWeilTheory
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{w} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type x} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H Picard Cycle : V → Type x}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (S : PreWeilTheory F TateLine V H Picard Cycle)
    (picardEquiv : ∀ X, (geometry.scheme.obj X).left.PicardGroup ≃+ Picard X) :
    let T := ChernTheory.ofPreWeilTheory S picardEquiv
    T.InitialAxioms →
      (Function.Bijective (algebraMap F (H point)) ∧
        ∀ X Y, Function.Bijective (T.kunnethMap X Y)) →
      (∃ gamma : T.CycleClass, ∀ X,
        Nonempty (geometry.scheme.obj X).left →
          EquidimensionalSpace (geometry.scheme.obj X).left →
          ∃ trace : H X →ₗ[F] F, T.IsNormalizedTrace gamma X trace) →
      (∀ {X' X : V} (b : X' ⟶ X) (I : (geometry.scheme.obj X).left.IdealSheafData),
        Smooth (I.subschemeι ≫ (geometry.scheme.obj X).hom) →
          IsBlowup (geometry.scheme.map b).left I → Function.Injective (T.pullback b)) →
      T.SatisfiesAxiomA8 → T.SatisfiesAxiomA9 → T.Axioms :=
  fun initial axiomA5 axiomA6 axiomA7 axiomA8 axiomA9 ↦
    ofInitialAxioms initial axiomA5 axiomA6 axiomA7 axiomA8 axiomA9

end Axioms

end ChernTheory
end WeilCohomology
