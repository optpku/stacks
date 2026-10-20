module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.LocalRepresentability

/-!
# Algebraic-space representability of quotient-stack Isom sheaves

The Isom sheaf between any two objects of an fppf quotient stack is represented
by an algebraic space over their base scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The Isom sheaf between any two objects of the fppf quotient stack of a groupoid
in algebraic spaces is represented by an algebraic space over their base scheme. -/
@[stacks 04TB]
theorem sheafHom_isAlgebraicSpace {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} (x y : (fppfQuotientStack G).p.Fiber T) :
    ∃ M : AlgebraicSpace T.left,
      Nonempty (AlgebraicSpace.toSheaf.obj M ≅ sheafHomOverLeft G x y) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
