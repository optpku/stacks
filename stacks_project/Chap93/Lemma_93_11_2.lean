/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.AlgebraicSpace.RimSchlessinger
import StacksCheckRecall

/-!
# Rim-Schlessinger condition for algebraic spaces

Example 93.11.1 satisfies (RS), so `Def_X` is a deformation category for
any algebraic space `X` over `k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Functor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : AlgebraicSpace (Spec (CommRingCat.of k)))

/- Lemma 93.11.2 (1)
Example 93.11.1 satisfies the Rim-Schlessinger condition (RS). -/
@[stacks 0E40]
#check (FlatAlgebraicSpaceCat.instHasRimSchlessinger_forget Λ k :
  HasRimSchlessinger (FlatAlgebraicSpaceCat.forget Λ k))

/- Lemma 93.11.2 (2)
In particular, `Def_X` is a deformation category for any algebraic space `X`
over `k`. -/
@[stacks 0E40]
#check (FlatAlgebraicSpaceCat.instIsDeformationCategory_deformationForget Λ k X :
  IsDeformationCategory (FlatAlgebraicSpaceCat.deformationForget Λ k X))
