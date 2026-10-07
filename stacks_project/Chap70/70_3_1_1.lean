module

public import ReasLib.AlgebraicGeometry.Scheme.Presheaf.Fiber.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite Limits AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Over

/- 70.3.1.1: For a transformation `a : F ⟶ G` of functors `(Over S)ᵒᵖ ⥤ Type`, a
scheme `T` over `S`, and a section `y : G.obj (op T)`, the fibre functor
`fiberFunctor a y` is the pullback of `Functor.whiskerLeft (Over.map T.hom).op a` against
the constant singleton (pre)sheaf, with the morphism from the singleton (pre)sheaf
given by `terminalSection y`. -/
@[stacks 049K] #check
  (AlgebraicGeometry.Scheme.Over.fiber_isPullback :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G)
      {T : Over S} (y : G.obj (op T)),
      IsPullback (fiber a y).ι
        ((Functor.isTerminalConst _ Types.isTerminalPUnit).from (fiberFunctor a y))
        (Functor.whiskerLeft (Over.map T.hom).op a) (terminalSection y))

end AlgebraicGeometry.Scheme.Over
