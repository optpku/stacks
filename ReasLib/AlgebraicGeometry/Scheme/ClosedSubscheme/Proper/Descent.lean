module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc
import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Proper

/-!
# Descent of proper closed subsets

Properness over a base for a closed subset descends along fpqc covering
families.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.ClosedSubset.IsProperOver

/-- If the inverse image of a closed subset is proper over every member of an fpqc covering
family, then the closed subset is proper over the base. -/
theorem of_fpqcCovering
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (Z : TopologicalSpace.Closeds X) {ι : Type v}
    (family : ι → Over Y) (hfamily : Scheme.FpqcCovering family)
    (hproper : ∀ i : ι, ClosedSubset.IsProperOver (pullback.snd f (family i).hom)
      (Z.preimage (pullback.fst f (family i).hom).continuous)) :
    ClosedSubset.IsProperOver f Z := sorry

end AlgebraicGeometry.ClosedSubset.IsProperOver
