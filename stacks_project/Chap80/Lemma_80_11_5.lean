/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Lemma_78_22_3

/-!
# Algebraic-space-hood of Isom sheaves on a quotient stack

If `B → S` and `(U, R, s, t, c)` are as in Definition 78.20.1 (1), then for any
scheme `T` over `S` and objects `x, y` of `[U/R]` over `T`, the sheaf
`Isom(x, y)` on `(Sch/T)_fppf` is an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace GroupoidAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 80.11.5. Assume `B → S` and `(U, R, s, t, c)` are as in
Definition 78.20.1 (1). For any scheme `T` over `S` and objects `x, y` of
`[U/R]` over `T`, the sheaf `Isom(x, y)` on `(Sch/T)_fppf` is an algebraic
space. Here `sheafHomOverLeft G x y` is `Isom(x, y)` on `(Sch/T)_fppf`, and
`uliftSheaf M ≅ sheafHomOverLeft G x y` encodes that this Type (u + 1) sheaf
is an algebraic space over `T`. -/
@[stacks 04TB]
theorem sheafHom_isAlgebraicSpace {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} (x y : (quotientStack G).p.Fiber T) :
    ∃ M : AlgebraicSpace T.left, Nonempty (uliftSheaf M ≅ sheafHomOverLeft G x y) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
