module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Presentation
import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.ChosenCovering
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 34.8.9: a big `ph` site is an explicit chosen small presentation
of the `ph` precoverage on schemes. -/
@[stacks 0DBJ] #check (AlgebraicGeometry.ChosenBigPhSite.{u, v} :
  Type (max (u + 1) (v + 1)))
