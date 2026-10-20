module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.TensorExtension

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe w u

namespace ModuleCat.PureExt

/-- The functorial pure extension groups, realized as extension groups between
tensor-extension functors in the abelian category of tensor-adequate module-valued
functors. -/
noncomputable def functor (A : CommRingCat.{u})
    [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [HasExt.{w} (ModuleValuedFunctor.TensorAdeq A)] (i : ℕ) :
    (ModuleCat.{u} A)ᵒᵖ ⥤ ModuleCat.{u} A ⥤ AddCommGrpCat.{w} :=
  (((Functor.whiskeringLeft₂ AddCommGrpCat.{w}).obj
    (ModuleValuedFunctor.TensorAdeq.tensorExtension A).op).obj
      (ModuleValuedFunctor.TensorAdeq.tensorExtension A)).obj
        (Abelian.extFunctor (C := ModuleValuedFunctor.TensorAdeq A) i)

/-- Evaluation of `functor A i` is the extension group between the corresponding
tensor-extension functors. -/
theorem functor_obj_obj (A : CommRingCat.{u})
    [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [HasExt.{w} (ModuleValuedFunctor.TensorAdeq A)] (i : ℕ)
    (M N : ModuleCat.{u} A) :
    ((functor A i).obj (op M)).obj N =
      AddCommGrpCat.of
        (Abelian.Ext ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj M)
          ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj N) i) := sorry

end ModuleCat.PureExt
