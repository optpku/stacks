module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Property
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.BoundedComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

/- Lemma 46.7.5: if `U = Spec A` is affine, then the canonical functor from the
bounded-below derived category of adequate module sheaves to the bounded-below derived
objects with adequate cohomology is an equivalence. -/
@[stacks 06ZV] #check
  (SheafOfModules.Adeq.boundedBelowComparisonIsEquivalence :
    ∀ (τ : StandardTopology) (A : CommRingCat.{u})
      [Abelian (RingedSite.ModuleCat.{u}
        (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
      [ObjectProperty.IsWeakSerreClass
        (SheafOfModules.Adeq.property (Scheme.Spec.obj (op A)) τ)]
      [HasDerivedCategory.{u} (RingedSite.ModuleCat.{u}
        (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
      [HasDerivedCategory.{u}
        (SheafOfModules.Adeq.property (Scheme.Spec.obj (op A)) τ).FullSubcategory],
      Functor.IsEquivalence
        (CategoryTheory.DerivedCategory.Plus.CohomologyIn.Comparison.functor
          (SheafOfModules.Adeq.property (Scheme.Spec.obj (op A)) τ)))
