module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Representability
import StacksCheckRecall

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

/- Lemma 80.11.5. Assume `B → S` and `(U, R, s, t, c)` are as in
Definition 78.20.1 (1). For any scheme `T` over `S` and objects `x, y` of
`[U/R]` over `T`, the sheaf `Isom(x, y)` on `(Sch/T)_fppf` is an algebraic
space. Here `sheafHomOverLeft G x y` is `Isom(x, y)` on `(Sch/T)_fppf`, and
`AlgebraicSpace.toSheaf.obj M ≅ sheafHomOverLeft G x y` encodes that this Type (u + 1) sheaf
is an algebraic space over `T`. -/
@[stacks 04TB]
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.sheafHom_isAlgebraicSpace :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      {T : Over S} (x y : (fppfQuotientStack G).p.Fiber T),
      ∃ M : AlgebraicSpace T.left,
        Nonempty (AlgebraicSpace.toSheaf.obj M ≅ sheafHomOverLeft G x y))

end AlgebraicGeometry.GroupoidAlgebraicSpace
