/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.Action.Module.Quasicoherent
public import stacks_project.Chap39.Lemma_39_16_1_ActionGroupoid

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.QCoh.Equivariant

/-- Compatibility spelling for the canonical comparison between pullback along a composite
and iterated pullback. -/
abbrev pullbackCompIso {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) :
    QCoh.pullback (f ≫ g) ≅ QCoh.pullback g ⋙ QCoh.pullback f :=
  GroupoidScheme.pullbackCompIso f g

end AlgebraicGeometry.Scheme.QCoh.Equivariant

variable {S : Scheme.{u}} (G : Grp (Over S)) (X : GroupScheme.Action G)

/- Compatibility check for the reusable category of equivariant quasi-coherent modules. -/
#check (Scheme.QCoh.Equivariant G X : Cat)
