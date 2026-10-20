module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Torsion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.RingedSpace

/- Lemma 20.55.3 (0GT5): for a locally principal regular ideal sheaf, first-power torsion,
all positive ideal-power torsion, monicity of the ideal action, chartwise generator regularity,
and stalkwise generator regularity are equivalent. -/
@[stacks 0GT5]
#check @IdealSheaf.IsRegularPrincipal.torsion_tfae

@[stacks 0GT5 "torsion by an ideal sheaf"]
#check @SheafOfModules.RingedSite.IdealSheaf.torsion

@[stacks 0GT5 "monomorphic ideal-sheaf action"]
#check @SheafOfModules.RingedSite.IdealSheaf.IsActionMono

@[stacks 0GT5 "regular action on principal charts"]
#check @IdealSheaf.ActsMonoLocally

@[stacks 0GT5 "regular action of stalk-ideal generators"]
#check @IdealSheaf.IsRegularOn
