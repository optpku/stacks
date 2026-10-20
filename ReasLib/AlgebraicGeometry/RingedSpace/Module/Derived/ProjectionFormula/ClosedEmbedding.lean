/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection formulas for closed embeddings of ringed spaces

For a morphism whose underlying map is a closed embedding, the canonical derived projection
formula holds without a perfectness restriction on `K ∈ D(𝒪_Y)`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X Y : RingedSpace.{u}}
variable [KFlat.HomotopyTensorDescends X] [KFlat.TensorDescends X]
variable [KFlat.IsLocalization X]
variable [KFlat.HomotopyTensorDescends Y] [KFlat.TensorDescends Y]
variable [KFlat.IsLocalization Y]
variable (f : X ⟶ Y)
variable [RingedSite.Hom.DerivedAdjunction.HasPair (opensRingedSiteHom f)]
variable [Functor.HasLeftDerivedFunctor
  (RingedSpace.modulePullbackToDerived f) (RingedSpace.ModuleQis Y)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Functor.Monoidal (L(f)^*)]

namespace ClosedEmbedding

/-- Lemma 20.54.4: the projection-formula mate along a closed embedding of ringed spaces is an
isomorphism for arbitrary derived modules. -/
@[stacks 0B55]
theorem isIso_projectionFormula
    (hf : Topology.IsClosedEmbedding f.hom.base)
    (K : ModuleDerived Y) (E : ModuleDerived X) :
    IsIso
      ((RingedSpace.modulePullbackDerivedPushforwardAdjunction f).leftProjectionFormulaMate E K) := sorry

/-- The right-oriented projection-formula mate along a closed embedding is an isomorphism for
arbitrary derived modules. -/
@[stacks 0B55 "right projection formula for closed embeddings"]
theorem isIso_projectionFormulaMate
    (hf : Topology.IsClosedEmbedding f.hom.base)
    (K : ModuleDerived Y) (E : ModuleDerived X) :
    IsIso
      ((RingedSpace.modulePullbackDerivedPushforwardAdjunction f).projectionFormulaMate K E) := sorry

/-- The canonical derived pullback-pushforward adjunction along a closed embedding satisfies the
right projection formula. -/
@[stacks 0B55 "projection-formula owner for closed embeddings"]
noncomputable def projectionFormula
    (hf : Topology.IsClosedEmbedding f.hom.base) :
    (RingedSpace.modulePullbackDerivedPushforwardAdjunction f).ProjectionFormula where
  isIso K E := isIso_projectionFormulaMate f hf K E

end ClosedEmbedding

end AlgebraicGeometry.RingedSpace.ModuleDerived
