module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.AffineEvaluation
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Underlying

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

namespace SheafOfModules

variable {S : Scheme.{u}} {τ : StandardTopology}

/--
The ordinary `AddCommGrpCat`-valued view of affine evaluation for a module sheaf.
-/
noncomputable def affineEvaluationUnderlying
    (ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S))
    (A : CommRingCat.{u}) (f : Scheme.Spec.obj (op A) ⟶ S) :
    Under A ⥤ AddCommGrpCat.{u} :=
  (ModuleValuedFunctor.forget A).obj (affineEvaluation ℱ.val A f)

/--
The affine-evaluation underlying view is the underlying functor of the bundled
affine-evaluation construction.
-/
theorem affineEvaluationUnderlying_eq
    (ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S))
    (A : CommRingCat.{u}) (f : Scheme.Spec.obj (op A) ⟶ S) :
    affineEvaluationUnderlying ℱ A f = (affineEvaluation ℱ.val A f).toFunctor := sorry

end SheafOfModules
