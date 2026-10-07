module

public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Category

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

namespace SheafOfModules.Adeq

/-- The canonical property of being an adequate module sheaf on the big `τ`-site of a
scheme. -/
abbrev property (S : Scheme.{u}) (τ : StandardTopology) :
    ObjectProperty
      (RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)) :=
  @SheafOfModules.IsAdequate S τ ModuleValuedFunctor.tensorExtensionUnderlying
    (@SheafOfModules.affineEvaluationUnderlying S τ)

/-- Membership in the canonical adequate-object property is adequacy on every member of an
affine `τ`-cover. -/
theorem property_iff (S : Scheme.{u}) (τ : StandardTopology)
    (ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)) :
    property S τ ℱ ↔
      ∃ (ι : Type u) (A : ι → CommRingCat.{u})
          (f : (i : ι) → Scheme.Spec.obj (op (A i)) ⟶ S),
        SemiRepresentableFamily.Over.IsCovering τ.precoverage
            (SemiRepresentableFamily.Over.ofArrows
              (fun i ↦ Scheme.Spec.obj (op (A i))) f) ∧
          ∀ i, Adequate (A i) (ModuleValuedFunctor.tensorExtensionUnderlying (A i))
            (SheafOfModules.affineEvaluationUnderlying ℱ (A i) (f i)) := sorry

/-- The canonical adequate-object property is a weak Serre class. -/
theorem propertyIsWeakSerreClass (S : Scheme.{u}) (τ : StandardTopology)
    [Abelian (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ S))] :
    ObjectProperty.IsWeakSerreClass (property S τ) := sorry

end SheafOfModules.Adeq
