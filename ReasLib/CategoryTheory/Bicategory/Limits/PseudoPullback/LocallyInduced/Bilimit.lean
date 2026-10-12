/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LocallyInduced.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Bilimit transfer for locally induced pseudopullback cones

This leaf contains only the universal-property criterion for lifting an ambient pseudopullback
bilimit to a locally induced bicategory. The forgetful data and computations live in the
preceding leaves.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe uA uB vB wB

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {A : Type uA} {B : Type uB} [Bicategory.{wB, vB} B]
variable {baseObj : A → B} {Q : Bicategory.HomProperty baseObj} [Q.IsMultiplicative]
variable {x y z : Bicategory.LocallyInducedBicategory B baseObj Q}
variable {f : x ⟶ z} {g : y ⟶ z}

/-- A pseudo-pullback bilimit in the ambient bicategory lifts to a locally induced bicategory
when its selected hom property is invariant under isomorphism and can be detected after
composition with the two projections. -/
theorem forgetLocallyInduced.isBilimit
    [Q.IsClosedUnderIsomorphisms]
    (P : PseudoPullbackCone f g)
    (hP : P.forgetLocallyInduced.IsBilimit)
    (h_detect : ∀ (t : Bicategory.LocallyInducedBicategory B baseObj Q)
        (k : baseObj t ⟶ baseObj P.pt),
      Q t x (k ≫ P.fst.obj) → Q t y (k ≫ P.snd.obj) → Q t P.pt k) :
    P.IsBilimit := sorry
/- Proof strategy: compare the induced cone comparison at `t` with the ambient comparison for
`P.forgetLocallyInduced`. Ambient bilimit gives an equivalence, while local fullness makes the
induced comparison fully faithful. For essential surjectivity, choose the ambient universal map
`k`. Its composites with the two projections are isomorphic to the selected legs of the competing
cone; closure of each `Q t _` under isomorphism puts both composites in `Q`, and `h_detect` then
puts `k` in `Q t P.pt`. Thus the ambient universal map lifts to the selected hom category, and
the resulting pointwise equivalences are exactly the field required by the
generic `ColaxCostructuredArrow.IsUniversal` owner. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
