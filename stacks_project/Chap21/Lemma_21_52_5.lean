module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Compact.Absolute
import StacksCheckRecall

/-!
Lemma 21.52.5 (tag `094D`).  For an object `U` of a ringed site, a uniform finite
cohomological-dimension bound for the module-sections functor together with preservation of
coproducts upgrades the degree-zero extension-by-zero generator `j_!𝒪_U[0]` to an ordinary compact
object.  The reusable statement is phrased through `ModuleCohomology.HasFiniteDimension` and
`ModuleCohomology.PreservesCoproducts`.
-/

@[expose] public section

open CategoryTheory

@[stacks 094D]
#check @RingedSite.Hom.ModuleDerived.LocalizedGenerator.isCompactObject_of_finiteDimension

#check @RingedSite.Hom.ModuleDerived.localizedGenerator
#check @RingedSite.Hom.ModuleCohomology.HasFiniteDimension
#check @RingedSite.Hom.ModuleCohomology.PreservesCoproducts
#check @CategoryTheory.isCompactObjectOn_top_iff

end
