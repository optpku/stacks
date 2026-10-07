module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology.IdealPower.MittagLeffler
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.22.1

The source argument is the one-parameter ideal-power quotient case.  Its reusable mathematical
content is owned by the positive presentation API: `Presentation` stores the ideal-power terms
and the short exact quotient rows, `Multiplication` stores the homogeneous maps, and
`SiteModuleCohomology.IdealPower.Action` installs the associated-graded action on the full
cohomology direct sum.  The chapter entry is intentionally recall-only; no chapter-local alias
is needed for downstream proofs.
-/

/- Lemma 21.22.1 (0GYQ): for a presented ideal-power quotient tower, Noetherianity of the graded
cohomology direct sum implies the Mittag-Leffler condition for the cohomology tower. -/
@[stacks 0GYQ]
#check @CategoryTheory.SiteModuleCohomology.IdealPower.isMittagLeffler_of_isNoetherian

/- The source rows and their ideal-power universal property. -/
#check @CategoryTheory.PNatInverseSystem.IdealPower.Presentation
#check @CategoryTheory.PNatInverseSystem.IdealPower.terms
#check @CategoryTheory.PNatInverseSystem.IdealPower.termInclusion
#check @CategoryTheory.PNatInverseSystem.IdealPower.Presentation.shortExact
#check @CategoryTheory.PNatInverseSystem.IdealPower.Presentation.isSMulSubobject
#check @CategoryTheory.PNatInverseSystem.IdealPower.Multiplication

/- The canonical cohomology grading and action used by the owner theorem. -/
#check @CategoryTheory.SiteModuleCohomology.piece
#check @CategoryTheory.SiteModuleCohomology.directSum
#check @CategoryTheory.SiteModuleCohomology.grade
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Action
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Action.smul_of
