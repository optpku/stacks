module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.CategoryTheory.Adjunction.Restriction
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.28.2

The source subcategory is the counit-isomorphism locus of the derived pullback--pushforward
adjunction. Repleteness, retract stability, triangulatedity, and full faithfulness of the
restricted right adjoint are owned by the reusable adjunction API.
-/

open CategoryTheory

/- Lemma 21.28.2 (0D7R): the counit-isomorphism locus of an adjunction with exact left adjoint is
a saturated triangulated strictly full subcategory, and the restricted right adjoint is fully
faithful. -/
@[stacks 0D7R]
#check @Adjunction.counitIsoProperty

@[stacks 0D7R]
#check @Adjunction.counitIsoProperty_isClosedUnderIsomorphisms

@[stacks 0D7R]
#check @Adjunction.counitIsoProperty_isStableUnderRetracts

@[stacks 0D7R]
#check @Adjunction.counitIsoProperty_isTriangulated

@[stacks 0D7R]
#check @Adjunction.counitIsoSubcategory

@[stacks 0D7R]
#check @Adjunction.rightAdjoint

@[stacks 0D7R]
#check @Adjunction.rightAdjoint_fullyFaithful

#check @RingedSite.Hom.moduleDerivedAdjunction

end
