/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf.BaseChange
public import stacks_project.Chap83.Lemma_83_3_2_QuotientSheaf

/-!
# Compatibility checks for quotient-sheaf base change
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U X X' : Over B}
variable (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) (f : X' ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.isInvariantHom_pullback_snd P hφ f :
  (P.baseChange hφ f).IsInvariantHom (pullback.snd φ f))

end AlgebraicGeometry.AlgebraicSpace.PreRelation
