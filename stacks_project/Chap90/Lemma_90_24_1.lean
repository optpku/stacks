/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_16_8_RimSchlessinger
public import stacks_project.Chap90.Definition_90_23_1
public import stacks_project.Chap90.Definition_90_25_1_Quotient
public import stacks_project.Chap90.Remark_90_16_5_SchlessingerH4

/-!
# Rim-Schlessinger for quotients of smooth groupoids in functors

If `(U, R, s, t, c)` is a smooth groupoid in functors on `ArtinianLocalAlgCat Λ k`
and the set-valued functors `U` and `R` satisfy (RS), then the quotient category
cofibered in groupoids `[U/R]` satisfies (RS).
-/

@[expose] public section

open CategoryTheory

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- Lemma 90.24.1: if `(U, R, s, t, c)` is a smooth groupoid in functors on
`ArtinianLocalAlgCat Λ k` and the set-valued functors `U` and `R` satisfy (RS), then
the quotient category cofibered in groupoids `[U/R]` satisfies (RS). -/
@[stacks 06KT]
theorem hasRimSchlessinger_quotient
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] (hU : Functor.HasSchlessingerH4 G.U)
    (hR : Functor.HasSchlessingerH4 G.R) :
    Functor.HasRimSchlessinger G.quotient.p := sorry

/-- The quotient `[U/R]` of a smooth groupoid in functors whose object and arrow
functors satisfy (RS) admits fibre products in the total category lying over
ring-level fibre products along a surjection. -/
theorem hasRimSchlessinger_quotient_spec
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] (hU : Functor.HasSchlessingerH4 G.U)
    (hR : Functor.HasSchlessingerH4 G.R) {x x1 x2 : G.quotient.total}
    (f1 : x1 ⟶ x) (f2 : x2 ⟶ x)
    (hf2 : Function.Surjective (G.quotient.p.map f2).hom) :
    ∃ (w : G.quotient.total) (π1 : w ⟶ x1) (π2 : w ⟶ x2),
      IsPullback π1 π2 f1 f2 ∧
        IsPullback (G.quotient.p.map π1) (G.quotient.p.map π2)
          (G.quotient.p.map f1) (G.quotient.p.map f2) := sorry

end CategoryTheory.GroupoidInFunctors
