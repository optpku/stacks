module

public import ReasLib.CategoryTheory.Monoidal.Flat
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
import StacksCheckRecall

/-!
# Definition 18.28.1

Flatness belongs to the monoidal-category layer: an object is flat when tensoring on the right
by it is exact.  Presheaves and sheaves of modules expose thin specializations of that owner.
-/

@[expose] public section

/- Definition 18.28.1 (03ER): the canonical categorical flat-object predicate. -/
@[stacks 03ER "categorical owner"]
#check @CategoryTheory.MonoidalCategory.IsFlat

/- Definition 18.28.1 (03ER): specialization to presheaves of modules. -/
@[stacks 03ER "presheaf modules"]
#check @PresheafOfModules.IsFlat

/- Definition 18.28.1 (03ER): specialization to sheaves of modules on a ringed site. -/
@[stacks 03ER "sheaves of modules"]
#check @SheafOfModules.RingedSite.IsFlat
