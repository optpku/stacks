/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap81.Lemma_81_10_8_BaseChange
public import stacks_project.Chap81.Lemma_81_10_8_Comparison
public import stacks_project.Chap81.Situation_81_10_6_FormalGlueing

/-!
# Lemma 81.10.8

In Situation 81.10.6, for a flat morphism `g : X' ⟶ X` of algebraic spaces, the
quasi-coherent pullbacks along `g` and along the induced maps of glueing
categories are compatible with `QCoh.FormalGlueing.functor` and with the reverse kernel
of a glueing triple.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

section
open QCoh.FormalGlueing

/-- Lemma 81.10.8 (1): In Situation 81.10.6, let `g : X' ⟶ X` be a flat morphism of
algebraic spaces, and write `Z' = pullback i g` and `Y' = pullback f g`. The
pullbacks `QCoh X ⥤ QCoh X'` and
`category f i ⥤ category (f' f g) (i' i g)` are compatible with
`functor`. -/
@[stacks 0AEZ, instance]
instance functorBaseChange_isIso {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] [Flat g] :
    IsIso (functorBaseChangeNatTrans f i g) :=
  sorry

end

section
open Modules
open Modules.FormalGlueing

/-- Lemma 81.10.8 (2): In Situation 81.10.6, let `g : X' ⟶ X` be a flat morphism of
algebraic spaces, and write `Z' = pullback i g` and `Y' = pullback f g`. The
pullbacks `QCoh X ⥤ QCoh X'` and the assignment of reverse kernels on glueing
triples are compatible with the reverse kernel. -/
@[stacks 0AEZ, instance]
instance reverseBaseChange_isIso {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] [Flat g] (H : (U i).Modules) (G : Y.Modules)
    (φ : (Modules.pullback (restrictF f i)).obj H ⟶ restrict G (j' f i))
    [H.IsQuasicoherent] [G.IsQuasicoherent] :
    IsIso (reverseBaseChangeHom f i g H G φ) :=
  sorry

end

end AlgebraicGeometry.AlgebraicSpace
