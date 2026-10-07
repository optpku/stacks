module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Ext.Limit
import StacksCheckRecall

/-!
# Lemma 15.103.1

@stack 0DYJ

Under the uniform ideal-power torsion hypothesis on higher Ext modules, the tower
`Ext^i_A(K, M / I^(n+1)M)` is essentially constant with value `Ext^i_A(K, M)` and has that
module as its limit.
-/

@[stacks 0DYJ "Ext tower over positive ideal-power quotients"]
#check @CategoryTheory.DerivedCategory.IdealPower.ExtQuotient.positiveTower

@[stacks 0DYJ "uniform ideal-power torsion of higher Ext"]
#check @CategoryTheory.DerivedCategory.IdealPower.ExtQuotient.IsPowerTorsionAbove

@[stacks 0DYJ "Lemma 15.103.1 essential constancy of Ext"]
#check @CategoryTheory.DerivedCategory.IdealPower.ExtQuotient.exists_essentiallyConstantCone

@[stacks 0DYJ "Lemma 15.103.1 limit of Ext"]
#check @CategoryTheory.DerivedCategory.IdealPower.ExtQuotient.exists_limitCone
