module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Tate
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom.Tate

/- Proposition 49.13.2: the unique Tate rule for the determinant of the naive
cotangent complex, preserving its canonical section and all open base-change
comparisons for locally quasi-finite syntomic morphisms of locally Noetherian schemes. -/
@[stacks 0FKD]
#check (AlgebraicGeometry.Scheme.Hom.Tate.existsUnique :
  ∃! r : ActualTate.Rule.{u}, ActualTate.IsRule r)

end Scheme.Hom.Tate
end AlgebraicGeometry
