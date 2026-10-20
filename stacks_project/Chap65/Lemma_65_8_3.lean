/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoproductSummand
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 65.8.3: if an algebraic space `X` over a scheme `S` is isomorphic, as an fppf sheaf on
`Over S`, to a coproduct of sheaves `F i`, then each summand is an algebraic space over `S`. -/
@[stacks 02WP] #check
  (AlgebraicGeometry.AlgebraicSpace.ofSheafCoprodSummand :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
      {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
      {c : Cofan F},
      IsColimit c →
        (X.functorOfPoints ≅ c.pt.obj) →
          I → AlgebraicSpace S)

end AlgebraicGeometry.AlgebraicSpace
