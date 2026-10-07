module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.OverStructurePresheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Example 59.15.10
   For every scheme `S`, the global-sections presheaf on schemes over `S`,
   viewed as a `RingCat`-valued presheaf, is a sheaf for the fpqc topology. -/
@[stacks 03O5] #check
  (AlgebraicGeometry.Scheme.overStructurePresheaf_isSheaf_fpqc :
    ∀ S : Scheme.{u},
      Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
        (S.overStructurePresheaf ⋙ forget₂ CommRingCat RingCat))
