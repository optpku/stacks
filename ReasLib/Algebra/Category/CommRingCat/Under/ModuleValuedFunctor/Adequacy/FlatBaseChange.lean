module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Linearity
public import Mathlib.Algebra.Category.ModuleCat.Descent

@[expose] public section

open CategoryTheory CategoryTheory.Limits RingHom

universe u v w

variable {A : CommRingCat.{u}}
variable {𝓕 : Type v} [Category.{w} 𝓕] [HasZeroMorphisms 𝓕] [HasKernels 𝓕]

namespace Adequate

/-- A base-change natural transformation is an isomorphism at an adequate object
when the algebra morphism is flat, both evaluation functors preserve zero morphisms
and finite limits, and the transformation is an isomorphism on every object in the
image of the presentation functor. -/
theorem baseChange_app_isIso
    (underline : ModuleCat.{u} A ⥤ 𝓕) {F : 𝓕} (hF : _root_.Adequate A underline F)
    {B B' : Under A} (f : B ⟶ B') (hflat : Flat f.right.hom)
    (evalB : 𝓕 ⥤ ModuleCat.{u} B.right) (evalB' : 𝓕 ⥤ ModuleCat.{u} B'.right)
    [evalB.PreservesZeroMorphisms] [PreservesFiniteLimits evalB]
    [evalB'.PreservesZeroMorphisms] [PreservesFiniteLimits evalB']
    (baseChange : evalB ⋙ ModuleCat.extendScalars f.right.hom ⟶ evalB')
    (baseChange_isIso : ∀ M, IsIso (baseChange.app (underline.obj M))) :
    IsIso (baseChange.app F) := sorry

end Adequate

namespace ModuleValuedFunctor.TensorAdequate

/-- Tensor adequacy of a module-valued functor implies flat base change. -/
theorem hasFlatBaseChange {A : CommRingCat.{u}} {F : ModuleValuedFunctor.bundled.{u, u} A}
    (hF : ModuleValuedFunctor.TensorAdequate F) : ModuleValuedFunctor.HasFlatBaseChange F := sorry

end ModuleValuedFunctor.TensorAdequate
