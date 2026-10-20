module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.Compact
import StacksCheckRecall

/-!
 Lemma 21.52.7 (tag `09JC`).  On a ringed site with a quasi-compact terminal object, cofinal
 finite coverings by quasi-compact objects, and quasi-compact pairwise fibre products for finite
 quasi-compact coverings, perfect derived modules are compact for bounded-below coproducts.  A
 finite module-cohomological-dimension bound at the terminal object upgrades this to ordinary
 compactness.
-/

@[expose] public section

open CategoryTheory

@[stacks 09JC "(1)"]
#check @RingedSite.Hom.ModuleDerived.IsPerfect.isCompactOnBoundedBelow_of_cofinalRefinement

@[stacks 09JC "(2)"]
#check @RingedSite.Hom.ModuleDerived.IsPerfect.isCompactObject_of_finiteDimension

#check @RingedSite.Hom.ModuleDerived.IsPerfect
#check @RingedSite.Hom.ModuleCohomology.HasFiniteDimension
#check @CategoryTheory.IsCompactObjectOn
#check @CategoryTheory.IsCompactObject

end
