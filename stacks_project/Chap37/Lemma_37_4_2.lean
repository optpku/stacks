/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Thickening.Torsion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AddSubgroup
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsThickening

variable {X X' : Scheme.{u}} (i : X ⟶ X') [IsThickening i]

/- Corrected Lemma 37.4.2 (tag 0C6S): the source statement omits the global-unit
obstruction. In addition to invertibility of `n`, require that the canonical map
on global units is surjective modulo `n`th powers. The source proof overlooks the
image of the connecting map from global units in the units cohomology sequence;
invertibility of `n` on ideal cohomology alone does not control its quotient. -/
@[stacks 0C6S] #check
  (AlgebraicGeometry.IsThickening.picardPullback_bijOn_torsionBy i :
    ∀ n : ℤ, IsUnit (n : Γ(X, ⊤)) →
      (∀ u : Γ(X, ⊤)ˣ, ∃ u' : Γ(X', ⊤)ˣ, ∃ v : Γ(X, ⊤)ˣ,
        u = Units.map i.appTop.hom.toMonoidHom u' * v ^ n) →
      Set.BijOn (Scheme.Hom.picardPullback i) X'.PicardGroup[n] X.PicardGroup[n])

end AlgebraicGeometry.IsThickening
