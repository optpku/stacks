/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalMap.Domain
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Definition 67.47.4: a rational map `φ` between algebraic spaces `X` and `Y` over a scheme
`S` is defined at a point `x ∈ |X|` exactly when some representative of `φ` has domain
containing `x`; `φ.domain` is the set of all such points. -/
@[stacks 0EMQ] #check
  (AlgebraicGeometry.AlgebraicSpace.RationalMap.mem_domain :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {φ : RationalMap X Y} {x : Points X},
      x ∈ φ.domain ↔ ∃ g : PartialMap X Y, x ∈ g.points ∧ g.toRationalMap = φ)

end AlgebraicGeometry.AlgebraicSpace
