module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Limit.WeaklyContractible
public import ReasLib.CategoryTheory.DerivedCategory.HomotopyLimit.Single
import StacksCheckRecall

@[expose] public section

/-!
# Proposition 21.51.2

The ordinary, derived-product, and Milnor consequences of having enough weakly contractible
objects are maintained by their reusable `ReasLib` owners.
-/

/- Proposition 21.51.2 (0947) (1): exactness of module sheaves is detected by sections on a
covering basis of weakly contractible objects. -/
@[stacks 0947 "(1)"]
#check @RingedSite.ModuleCat.WeaklyContractible.exact_iff_evaluation

/- Proposition 21.51.2 (0947) (2): every compatible comparison with the lower-truncation
homotopy limit is an isomorphism. -/
@[stacks 0947 "(2)"]
#check @RingedSite.Hom.ModuleDerived.Limit.Comparison.isIso_of_enoughWeaklyContractible

/- Proposition 21.51.2 (0947) (3): an inverse system with epimorphic transitions has an
epimorphic projection from its limit to the zeroth stage. -/
@[stacks 0947 "(3)"]
#check @RingedSite.ModuleCat.WeaklyContractible.limit_π_zero_epi

/- Proposition 21.51.2 (0947) (4): products of module sheaves are exact. -/
@[stacks 0947 "(4)"]
#check @RingedSite.ModuleCat.WeaklyContractible.ab4Star

/- Proposition 21.51.2 (0947) (5): localization to the derived category preserves products of
representative complexes. -/
@[stacks 0947 "(5)"]
#check @RingedSite.Hom.ModuleDerived.Limit.Product.q_preservesProduct_of_enoughWeaklyContractible

/- Proposition 21.51.2 (0947) (6): a homotopy limit of degree-zero objects has no cohomology in
degrees strictly greater than one. -/
@[stacks 0947 "(6), upper vanishing"]
#check @CategoryTheory.HomotopyLimit.IsOf.single_homology_isZero_of_gt

/- The degree-one term in (6) is the canonical Milnor cokernel. -/
@[stacks 0947 "(6), first derived limit"]
#check @CategoryTheory.HomotopyLimit.IsOf.single_homology_succ_isomorphic_canonicalR1

/- The canonical first derived limit is the cokernel of the Milnor difference map. -/
@[stacks 0947 "(6), cokernel formula"]
#check @CategoryTheory.SequentialInverseSystem.Milnor.ProductCone.canonicalR1.eq_cokernel

/- Proposition 21.51.2 (0947) (7): cohomology of a sequential homotopy limit lies in the
canonical Milnor short exact sequence. -/
@[stacks 0947 "(7)"]
#check @CategoryTheory.HomotopyLimit.IsOf.cohomologyShortExact
