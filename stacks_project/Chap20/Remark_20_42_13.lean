module

public import ReasLib.CategoryTheory.Monoidal.Closed.OplaxMonoidal
public import ReasLib.CategoryTheory.Monoidal.Closed.PullbackComparison
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

/- Remark 20.42.13 (08I3) is the ringed-space specialization of the generic oplax-monoidal
internal-Hom comparison.  A strong monoidal derived pullback supplies the oplax instance
automatically, so the tensor comparison is not repeated as a forced argument here. -/
@[stacks 08I3]
#check @CategoryTheory.Functor.PullbackInternalHom.comparison

#check @CategoryTheory.Functor.PullbackInternalHom.evaluation
#check @CategoryTheory.Functor.PullbackInternalHom.comparison_spec

/- When the derived pullback carries a strong monoidal instance, the same construction is
available without passing the tensor comparison explicitly. -/
#check @CategoryTheory.Functor.OplaxMonoidal.InternalHom.comparison

end AlgebraicGeometry.RingedSpace
