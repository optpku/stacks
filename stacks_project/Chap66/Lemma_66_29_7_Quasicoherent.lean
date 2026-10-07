module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Properties
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap66.Lemma_66_29_7_CommSheaf

/-!
# Closure properties of quasi-coherent modules on algebraic spaces

Quasi-coherent `𝒪_X`-modules on an algebraic space are closed under coproducts, colimits,
kernels, cokernels, and short-exact two-out-of-three implications, and the tensor product of
quasi-coherent modules remains quasi-coherent. Internal Hom from a finitely presented
quasi-coherent module into a quasi-coherent module is quasi-coherent.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.MonoidalClosed CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace

/-- The category of `𝒪_X`-modules on the small étale site of an algebraic space is abelian. -/
instance modulesAbelian {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Abelian X.Modules where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

namespace QCoh

/-- Quasi-coherent modules on an algebraic space are closed under colimits of every
universe-compatible shape. -/
instance closedUnderColimitsOfShape {S : Scheme.{u}} (X : AlgebraicSpace S)
    (J : Type v) [Category.{w} J] :
    (quasiCoherentModuleProperty X).IsClosedUnderColimitsOfShape J :=
  sorry

/-- Quasi-coherent modules on an algebraic space form a weak Serre class, so they are closed
under kernels, cokernels, and short-exact two-out-of-three implications. -/
instance isWeakSerreClass {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (quasiCoherentModuleProperty X).IsWeakSerreClass :=
  sorry

end QCoh

namespace Modules

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- A coproduct of quasi-coherent modules on an algebraic space is quasi-coherent. -/
instance isQuasicoherent_coproduct {ι : Type v} (F : ι → X.Modules)
    [HasCoproduct F] [∀ i, (F i).IsQuasicoherent] :
    (∐ F).IsQuasicoherent :=
  sorry

/-- A colimit of a diagram of quasi-coherent modules on an algebraic space is quasi-coherent. -/
theorem isQuasicoherent_colimit {J : Type v} [Category.{w} J]
    (F : J ⥤ X.Modules) [HasColimit F]
    (hF : ∀ j, (F.obj j).IsQuasicoherent) :
    (colimit F).IsQuasicoherent :=
  sorry

variable {X}

/-- The kernel of a morphism of quasi-coherent modules on an algebraic space is quasi-coherent. -/
instance isQuasicoherent_kernel {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G) :
    (kernel f).IsQuasicoherent :=
  sorry

/-- The cokernel of a morphism of quasi-coherent modules on an algebraic space is
quasi-coherent. -/
instance isQuasicoherent_cokernel {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G) :
    (cokernel f).IsQuasicoherent :=
  sorry

/-- The tensor product of quasi-coherent modules on the small étale site of an algebraic space
is quasi-coherent. -/
instance isQuasicoherent_tensor
    (F G : RingedSite.ModuleCat.{u} (commRingedSite X))
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (SheafOfModules.RingedSite.moduleTensor F G).IsQuasicoherent :=
  sorry

/-- Internal Hom from a finitely presented module to a quasi-coherent module on the small étale
site of an algebraic space is quasi-coherent. -/
instance isQuasicoherent_internalHom
    (F G : RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X))
    [F.IsFinitePresentation] [G.IsQuasicoherent] :
    ((ihom F).obj G).IsQuasicoherent :=
  sorry

end Modules

end AlgebraicGeometry.AlgebraicSpace
