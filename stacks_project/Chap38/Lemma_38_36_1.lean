module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Blowup
public import stacks_project.Chap38.«38_36_0_1»
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 38.36.1: a sheaf on the big ph site over `S` sends a blowup square to a
pullback square of types. Here `sq.X₁`, `sq.X₂`, `sq.X₃`, and `sq.X₄` represent
`E`, `X'`, `Z`, and `X`, respectively. -/
@[stacks 0EW1] #check
  (AlgebraicGeometry.Scheme.Ph.Sheaf.map_isPullback_of_isBlowup :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (F : CategoryTheory.Sheaf (AlgebraicGeometry.Scheme.bigPhSite S) (Type v))
      (sq : Square (Over S))
      [AlgebraicGeometry.IsClosedImmersion sq.f₃₄.left]
      [AlgebraicGeometry.LocallyOfFinitePresentation sq.f₃₄.left]
      (h_pullback : (sq.map (Over.forget S)).IsPullback)
      [AlgebraicGeometry.IsBlowup sq.f₂₄.left (sq.f₃₄.left).ker],
      (sq.op.map F.obj).IsPullback)
