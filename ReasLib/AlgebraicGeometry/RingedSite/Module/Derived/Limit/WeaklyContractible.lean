module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Limit.Truncation
public import ReasLib.AlgebraicGeometry.RingedSite.Module.WeaklyContractible
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Products
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Single
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived completeness from weakly contractible objects

Weakly contractible objects provide the local negative-degree vanishing needed by the lower-
truncation comparison criterion.  This leaf keeps that specialization separate from the generic
basiswise criterion.
-/

open CategoryTheory CategoryTheory.Limits Opposite
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

noncomputable section

universe t z u v w

namespace RingedSite.Hom.ModuleDerived.Limit

variable (X : RingedSite.{u, v, w})
variable [UnivLE.{max u v, z}]

namespace Basis

variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{z} X)]

/-- A weakly contractible object satisfies the local negative-degree vanishing predicate for
every derived module. -/
@[stacks 0947 "negative vanishing on weakly contractible objects"]
theorem negative_of_isWeaklyContractible
    (E : ModuleDerived.{z} X) {V : X}
    (hV : X.siteTopology.IsWeaklyContractible V) :
    negative X E V := sorry

end Basis

namespace Comparison

variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{z} X)]

/-- If a ringed site has enough weakly contractible objects, every compatible lower-truncation
derived-limit comparison is an isomorphism. -/
@[stacks 0947 "derived completeness from weakly contractible objects"]
theorem isIso_of_enoughWeaklyContractible
    (E K : ModuleDerived.{z} X) (c : E ⟶ K)
    (hc : CategoryTheory.DerivedCategory.Truncation.Lower.Comparison.Exists E c)
    (hEnough : X.siteTopology.HasEnoughObjectsWithProperty
      X.siteTopology.IsWeaklyContractible) :
    IsIso c := sorry

end Comparison

namespace Product

/-- Under enough weakly contractible objects, localization to the derived category preserves a
product of representative complexes of any prescribed shape.  The shape-wise product instance
is an explicit input, while exactness is supplied by the weakly-contractible hypothesis. -/
@[stacks 0947 "derived products from weakly contractible objects"]
theorem q_preservesProduct_of_enoughWeaklyContractible
    {T : Type t}
    [HasProductsOfShape T (RingedSite.ModuleCat.{z} X)]
    (hEnough : X.siteTopology.HasEnoughObjectsWithProperty
      X.siteTopology.IsWeaklyContractible)
    (I : T → CochainComplex (RingedSite.ModuleCat.{z} X) ℤ) :
    PreservesLimit (Discrete.functor I)
      (DerivedCategory.Q :
        CochainComplex (RingedSite.ModuleCat.{z} X) ℤ ⥤
          ModuleDerived.{z} X) := sorry

end Product

namespace Single

/-- Under enough weakly contractible objects, the upper cohomology vanishing for a tower of
degree-zero module sheaves is available without exposing the exact-product construction used in
its proof. -/
@[stacks 0947 "single-tower upper vanishing"]
theorem homology_isZero_of_enoughWeaklyContractible
    [HasCountableProducts (RingedSite.ModuleCat.{z} X)]
    (hEnough : X.siteTopology.HasEnoughObjectsWithProperty
      X.siteTopology.IsWeaklyContractible)
    (F : SequentialInverseSystem (RingedSite.ModuleCat.{z} X))
    (K : ModuleDerived.{z} X)
    (hK : IsDerivedLimit
      (F ⋙ DerivedCategory.singleFunctor (RingedSite.ModuleCat.{z} X) (0 : ℤ)) K)
    (p : ℤ) (hp : 1 < p) :
    IsZero ((DerivedCategory.homologyFunctor (RingedSite.ModuleCat.{z} X) p).obj K) := sorry

/-- Under enough weakly contractible objects, degree-one cohomology of a degree-zero tower is the
first derived inverse limit of that tower. -/
@[stacks 0947 "single-tower first derived limit"]
theorem homology_one_isomorphic_of_enoughWeaklyContractible
    [HasCountableProducts (RingedSite.ModuleCat.{z} X)]
    (hEnough : X.siteTopology.HasEnoughObjectsWithProperty
      X.siteTopology.IsWeaklyContractible)
    (F : SequentialInverseSystem (RingedSite.ModuleCat.{z} X))
    (K : ModuleDerived.{z} X)
    (hK : IsDerivedLimit
      (F ⋙ DerivedCategory.singleFunctor (RingedSite.ModuleCat.{z} X) (0 : ℤ)) K) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor (RingedSite.ModuleCat.{z} X) (1 : ℤ)).obj K)
      F.firstDerivedLimit := sorry

end Single

end RingedSite.Hom.ModuleDerived.Limit

end
