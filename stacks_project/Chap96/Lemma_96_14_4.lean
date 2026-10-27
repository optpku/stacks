/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quotient.QuasicoherentHom
import StacksCheckRecall

/-!
# Lemma 96.14.4

For a groupoid in algebraic spaces with flat, locally finitely presented source
and target, atlas restriction of morphisms from a quasi-coherent module to an
arbitrary module is injective and its image is characterized by the canonical
small-étale comparison diagram.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.GroupoidAlgebraicSpace

universe u

/- Lemma 96.14.4 (1): Restriction along the quotient atlas is injective on
morphisms from a quasi-coherent module to an arbitrary module. -/
@[stacks 076S] #check
  (AlgebraicGeometry.GroupoidsOver.atlasRestrictHom_injective :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      (F : QCoh (SmallQuotient.quotientStack G))
      (H : RingedSite.ModuleCat.{u} (ringedSite (SmallQuotient.quotientStack G)))
      [AlgebraicSpace.Flat G.s.left]
      [AlgebraicSpace.LocallyOfFinitePresentation G.s.left]
      [AlgebraicSpace.Flat G.t.left]
      [AlgebraicSpace.LocallyOfFinitePresentation G.t.left],
      Function.Injective (atlasRestrictHom G F.obj H))

/- Lemma 96.14.4 (2): The image consists exactly of the maps giving a commutative
small-étale comparison diagram, with the middle modules identified by the
canonical source–target isomorphism of the quotient atlas. -/
@[stacks 076S] #check
  (AlgebraicGeometry.GroupoidsOver.mem_range_atlasRestrictHom_iff :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      (F : QCoh (SmallQuotient.quotientStack G))
      (H : RingedSite.ModuleCat.{u} (ringedSite (SmallQuotient.quotientStack G)))
      [AlgebraicSpace.Flat G.s.left]
      [AlgebraicSpace.LocallyOfFinitePresentation G.s.left]
      [AlgebraicSpace.Flat G.t.left]
      [AlgebraicSpace.LocallyOfFinitePresentation G.t.left]
      (φ : atlasRestrictModules G F.obj ⟶ atlasRestrictModules G H),
      (∃ ψ : F.obj ⟶ H, atlasRestrictHom G F.obj H ψ = φ) ↔
        RespectsComparisons G F.obj H φ)
