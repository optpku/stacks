/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.FullyFaithful
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.SchemeOverField.PerfectDerived

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/- Lemma 57.11.5: for a field `k` and proper `k`-schemes `X`, `Y` with `X` regular, a
`k`-linear exact functor `F : PerfectDerived X ⥤ PerfectDerived Y` is fully faithful if and
only if for all closed points `x`, `x'` of `X` and all `i : ℤ`, the maps
`Hom(𝒪_x, 𝒪_{x'}⟦i⟧) ⟶ Hom(F(𝒪_x), F(𝒪_{x'})⟦i⟧)` are isomorphisms, where `𝒪_x` is the
`κ(x)`-valued skyscraper at `x`. -/
@[stacks 0G25] #check
  (AlgebraicGeometry.SchemeOverField.PerfectDerived.fullyFaithful_iff_map_ext_residueFieldSkyscraper :
    ∀ {k : Type u} [Field k] (X Y : SchemeOverField k)
      [IsProper X.hom] [IsProper Y.hom] [Scheme.Regular X.left]
      (F : PerfectDerived X ⥤ PerfectDerived Y) [F.Linear k] [F.CommShift ℤ]
      [F.IsTriangulated],
    Nonempty F.FullyFaithful ↔
      ∀ (x x' : X.left) (hx : x ∈ closedPoints X.left) (hx' : x' ∈ closedPoints X.left)
        (i : ℤ),
        Function.Bijective
          (fun f : residueFieldSkyscraper X x hx ⟶ residueFieldSkyscraper X x' hx'⟦i⟧ ↦
            ShiftedHom.map f F))

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
