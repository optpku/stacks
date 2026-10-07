module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.CanonicalComparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.RelativeDifferentials

/- Lemma 50.18.6 (1): the unique differential-form comparison rule for the
fixed determinant of the naive cotangent complex, on arbitrary schemes. -/
@[stacks 0FLA]
#check (AlgebraicGeometry.Scheme.RelativeDifferentials.existsUniqueComparisonRule :
  ∃! r : ComparisonRule.{u}, IsComparisonRule r)

/- Lemma 50.18.6 (2): the comparison after absolute-form pullback is tensor multiplication by delta. -/
@[stacks 0FLA]
#check (AlgebraicGeometry.Scheme.RelativeDifferentials.ComparisonRule.absoluteFormComparison_comp_component :
  ∀ (r : ComparisonRule.{u}) (hr : IsComparisonRule r)
    {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyQuasiFinite f] [Syntomic f] (p : ℕ),
    absoluteFormComparison f p ≫ r.component f p =
      RingedSpace.tensorSectionHom
        ((Scheme.Modules.pullback f).obj (Λ[p] Ω[(terminal.from X).toShHom]))
        (ActualTate.detNL f) (ActualTate.delta f))

end Scheme.RelativeDifferentials
end AlgebraicGeometry
