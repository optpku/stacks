/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.InDimensions
public import ReasLib.AlgebraicGeometry.Scheme.Flattening.FreeAtGenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Finite rank decomposition of the flat-in-dimensions functor

The coproduct is described by clopen rank partitions of each test scheme. In particular, a
section may have different ranks on different clopen pieces, and the empty test scheme has
one section. A pointwise coproduct of the underlying presheaves does not have this behaviour.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Flattening

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)

/-- The clopen piece on which the rank label is `p`, viewed as an open subscheme of `T`. -/
def rankPartitionOpen {c : ℕ} (T : Over S)
    (r : LocallyConstant T.left (Fin (c + 1))) (p : Fin (c + 1)) : T.left.Opens :=
  ⟨r ⁻¹' {p}, r.isLocallyConstant {p}⟩

section RankPartitions

variable [Smooth f] [GeometricallyIrreducible f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]

/-- A rank partition carries the actual generic-point rank condition on each clopen piece.
The structural map of the `p`-piece is its open immersion followed by `T.hom`. -/
def IsGenericRankPartition {c : ℕ} (T : Over S)
    (r : LocallyConstant T.left (Fin (c + 1))) : Prop :=
  ∀ p : Fin (c + 1), IsFreeAtGenericPoints f ℱ p
    (Over.mk ((rankPartitionOpen T r p).ι ≫ T.hom))

/-- Pullback takes inverse images of the clopen rank pieces and pulls back their `H_p` sections.
Only the preservation proof is required here; the rank labels are explicitly precomposed. -/
theorem IsGenericRankPartition.pullback {c : ℕ} {T T' : Over S} (g : T' ⟶ T)
    {r : LocallyConstant T.left (Fin (c + 1))} (h : IsGenericRankPartition f ℱ T r) :
    IsGenericRankPartition f ℱ T' (LocallyConstant.comap g.left.base.hom r) := sorry

/-- The finite coproduct of the rank functors, expressed as clopen partitions with an `H_p`
section on each piece. This explicit functor stays in `Type u` and uses no sheafification
existence assumption. -/
def rankCoproductFunctor (c : ℕ) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := {r : LocallyConstant T.unop.left (Fin (c + 1)) //
    IsGenericRankPartition f ℱ T.unop r}
  map g := ↾fun s ↦ ⟨LocallyConstant.comap g.unop.left.base.hom s.val,
    IsGenericRankPartition.pullback f ℱ g.unop s.property⟩
  map_id T := by
    apply TypeCat.homEquiv.injective
    funext s
    apply Subtype.ext
    exact LocallyConstant.ext (fun _ ↦ rfl)
  map_comp g h := by
    apply TypeCat.homEquiv.injective
    funext s
    apply Subtype.ext
    exact LocallyConstant.ext (fun _ ↦ rfl)

variable (d : ℕ) [Scheme.Hom.RelativeDimension f d]

/-- The local `H_p` conditions imply flatness in dimensions at least `d`; the clopen pieces
cover the entire test scheme. -/
theorem IsGenericRankPartition.flatInDimensionsGE {c : ℕ} (T : Over S)
    {r : LocallyConstant T.left (Fin (c + 1))} (h : IsGenericRankPartition f ℱ T r) :
    Modules.flatOverInDimensionsGE
      (Modules.baseChangeModule f T.hom ℱ) (pullback.snd f T.hom) d := sorry

/-- The canonical comparison glues the terminal sections supplied by the rank pieces.
Its underlying value is always `PUnit.unit`; its proof is the local-to-global flatness lemma. -/
def rankCoproductToFlatInDimensions (c : ℕ) :
    rankCoproductFunctor f ℱ c ⟶ flatInDimensionsFunctor f ℱ d where
  app T := ↾fun s ↦ ⟨PUnit.unit,
    IsGenericRankPartition.flatInDimensionsGE f ℱ d T.unop s.property⟩
  naturality _ _ g := by
    apply TypeCat.homEquiv.injective
    funext s
    apply Subtype.ext
    rfl

end RankPartitions

variable (d : ℕ)
variable [IsAffine X] [IsAffine S] [Smooth f] [GeometricallyIrreducible f]
  [Scheme.Hom.RelativeDimension f d] [ℱ.IsFinitePresentation]

/-- For a smooth affine family with geometrically irreducible fibres of dimension `d`, the
canonical comparison from the clopen rank coproduct to the flat-in-dimensions functor is an
isomorphism for some finite rank bound. Its inverse labels each point by the unique local
free rank near its fibre generic point, so it also applies to disconnected or empty tests. -/
theorem existsFlatInDimensionsIsoRankCoproduct :
    ∃ c : ℕ, IsIso (rankCoproductToFlatInDimensions f ℱ d c) := sorry

end AlgebraicGeometry.Scheme.Flattening
