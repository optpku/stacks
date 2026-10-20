/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Length
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Length.GeometricPoint
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Definition 82.4.2: let `S` be a scheme and let `X` be an algebraic space over `S`.
Let `F` be a quasi-coherent `𝒪_X`-module. Let `x ∈ |X|`. Let `d : ℕ∞`. We say `F`
has length `d` at `x` if the equivalent conditions of Lemma 82.4.1 are satisfied. -/
@[stacks 0EE2]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.hasLengthAt :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, X.Modules → Points X → ℕ∞ → Prop)

#check AlgebraicGeometry.AlgebraicSpace.Modules.lengthAt_tfae
#check AlgebraicGeometry.AlgebraicSpace.Modules.hasLengthAt_iff
#check AlgebraicGeometry.AlgebraicSpace.Modules.exists_lengthAtGeometricPoint_iff
#check AlgebraicGeometry.AlgebraicSpace.Modules.exists_lengthOnEtaleChart_iff_forall
