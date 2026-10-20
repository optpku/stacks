module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Different
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Remark 49.14.2: the different of a quasi-finite morphism of Noetherian schemes may be formed
without global flatness from a global section of the relative dualizing sheaf, once the flat
locus contains the associated points of the source and the inverse image of the associated points
of the target. -/
@[stacks 0BWM] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.different :
    {X Y : Scheme.{u}} → {f : Y ⟶ X} →
    [IsLocallyNoetherian X] → [IsLocallyNoetherian Y] →
    [LocallyOfFiniteType f] → [LocallyQuasiFinite f] →
    (W : f.RelativeDualizingSheaf) → (τ : W.module.obj.sections) → Y.IdealSheafData)

#check AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.associatedPoints_subset_flatOpen
#check AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.sections_eq_of_restrict_eq
