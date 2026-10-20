/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Reduced
import StacksCheckRecall

/-!
# Reducedness of blowups of reduced algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.17.7: let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `I ⊂ 𝒪_X` be a quasi-coherent sheaf of ideals. If `X` is reduced, then the
blowup of `X` in `I` is reduced. -/
@[stacks 085W] #check
  (AlgebraicGeometry.AlgebraicSpace.Blowup.isReduced :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I) [IsReduced X],
      IsReduced π.space)
