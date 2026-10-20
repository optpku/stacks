module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Property
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison.Plus

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.DerivedCategory.Plus.CohomologyIn
open AlgebraicGeometry

noncomputable section

universe u

namespace SheafOfModules.Adeq

/-- On the affine scheme `Spec A`, the bounded-below comparison functor induced by the
canonical adequate-object property is an equivalence. -/
theorem boundedBelowComparisonIsEquivalence
    (τ : StandardTopology) (A : CommRingCat.{u})
    [Abelian (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [ObjectProperty.IsWeakSerreClass (property (Scheme.Spec.obj (op A)) τ)]
    [HasDerivedCategory.{u} (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [HasDerivedCategory.{u}
      (property (Scheme.Spec.obj (op A)) τ).FullSubcategory] :
    Functor.IsEquivalence
      (Comparison.functor (property (Scheme.Spec.obj (op A)) τ)) := sorry

end SheafOfModules.Adeq
