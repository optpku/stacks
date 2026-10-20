/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.FormalObjectSystem
public import stacks_project.Chap99.Situation_99_16_3

/-!
# Lemma 99.16.11

In Situation 99.16.3, if `B = S` is locally Noetherian, then strong formal
effectiveness in the sense of Artin's Axioms, Remark 98.20.2 holds for
`p : Complexes f ⥤ Over S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Complexes

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

/-- Lemma 99.16.11: in Situation 99.16.3, if `B = S` is locally Noetherian,
then every compatible system of objects of `Complexes f` over spectra of a
sequential inverse system of algebras with surjective locally nilpotent
transitions is effective over the spectrum of the inverse limit. -/
@[stacks 0DLM]
theorem strongFormalEffectiveness {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : AlgebraicSpace S} (f : X ⟶ ofOver (Over.mk (𝟙 S)))
    [∀ σ : SchemeOver (ofOver (Over.mk (𝟙 S))), ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ σ : SchemeOver (ofOver (Over.mk (𝟙 S))), ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f]
    (ξ : FormalObjectSystem (p f)) :
    ξ.IsEffective := sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
