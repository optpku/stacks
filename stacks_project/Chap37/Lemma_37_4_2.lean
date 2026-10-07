module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Thickening.Torsion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AddSubgroup
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsThickening

variable {X X' : Scheme.{u}} (i : X ⟶ X') [IsThickening i]

/- Lemma 37.4.2: if `n` is invertible in `Γ(X, ⊤)`, pullback along a thickening
bijects the `n`-torsion subgroups of the Picard groups of `X'` and `X`. -/
@[stacks 0C6S] #check
  (AlgebraicGeometry.IsThickening.picardPullback_bijOn_torsionBy i :
    ∀ n : ℤ, IsUnit (n : Γ(X, ⊤)) →
      Set.BijOn (Scheme.Hom.picardPullback i) X'.PicardGroup[n] X.PicardGroup[n])

end AlgebraicGeometry.IsThickening
