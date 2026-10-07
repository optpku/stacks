module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import ReasLib.CategoryTheory.Sites.Family.Covering
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u z

namespace SheafOfModules

variable {S : Scheme.{u}} {τ : StandardTopology}

/-- A big-site module sheaf is adequate when one affine `τ`-cover of the base
makes every affine-evaluation functor adequate relative to the specified
module-valued extension functors. -/
def IsAdequate
    (underline : (A : CommRingCat.{u}) →
      ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{z}))
    (affineEvaluation :
      RingedSite.ModuleCat.{z} (StandardTopology.Big.ringedSite τ S) →
        (A : CommRingCat.{u}) → (Scheme.Spec.obj (op A) ⟶ S) →
          Under A ⥤ AddCommGrpCat.{z})
    (ℱ : RingedSite.ModuleCat.{z} (StandardTopology.Big.ringedSite τ S)) : Prop :=
  ∃ (ι : Type u) (A : ι → CommRingCat.{u})
      (f : (i : ι) → Scheme.Spec.obj (op (A i)) ⟶ S),
    SemiRepresentableFamily.Over.IsCovering τ.precoverage
        (SemiRepresentableFamily.Over.ofArrows
          (fun i ↦ Scheme.Spec.obj (op (A i))) f) ∧
      ∀ i, Adequate (A i) (underline (A i)) (affineEvaluation ℱ (A i) (f i))

/-- Adequacy is characterized by the existence of an affine `τ`-cover on whose
members all affine-evaluation functors have adequate kernel presentations. -/
theorem isAdequate_iff
    (underline : (A : CommRingCat.{u}) →
      ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{z}))
    (affineEvaluation :
      RingedSite.ModuleCat.{z} (StandardTopology.Big.ringedSite τ S) →
        (A : CommRingCat.{u}) → (Scheme.Spec.obj (op A) ⟶ S) →
          Under A ⥤ AddCommGrpCat.{z})
    (ℱ : RingedSite.ModuleCat.{z} (StandardTopology.Big.ringedSite τ S)) :
    IsAdequate underline affineEvaluation ℱ ↔
      ∃ (ι : Type u) (A : ι → CommRingCat.{u})
          (f : (i : ι) → Scheme.Spec.obj (op (A i)) ⟶ S),
        SemiRepresentableFamily.Over.IsCovering τ.precoverage
            (SemiRepresentableFamily.Over.ofArrows
              (fun i ↦ Scheme.Spec.obj (op (A i))) f) ∧
          ∀ i, Adequate (A i) (underline (A i)) (affineEvaluation ℱ (A i) (f i)) := sorry

end SheafOfModules
