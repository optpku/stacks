module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-variable derived tensor for module sheaves

This file specializes the generic total-left-derived tensor bifunctor to modules over a
commutative ring sheaf.  The site and structure sheaf are the public parameters; the underlying
abelian and monoidal module-category infrastructure remains inferred.
-/

@[expose] public section

open CategoryTheory ComplexShape
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

-- Local instance justification (defeq pin): tensor also elaborates the commutative-sheaf presentation, using the same canonical derived category.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived.Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf J CommRingCat.{w})
variable [ModuleDerived.KFlat.HomotopyTensorDescends O]

/-- The existence condition for the two-variable derived tensor of module sheaves. -/
@[stacks 0FPH "ringed-site derived tensor existence"]
abbrev Has : Prop :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Has
    (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf J O))

/-- Totalized tensor on the homotopy category of module sheaves, followed by localization. -/
@[stacks 0FPH "ringed-site homotopy tensor source functor"]
abbrev sourceFunctor :
    (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf J O) ×
        ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf J O)) ⥤
      ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O) :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.sourceFunctor
    (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf J O))

/-- Pairs of quasi-isomorphisms used to derive tensor in both variables. -/
@[stacks 0FPH "ringed-site derived tensor denominators"]
abbrev qis : MorphismProperty
    (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf J O) ×
      ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf J O)) :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.qis
    (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf J O))

/-- The product localization from pairs of module homotopy objects to pairs of module-derived
objects. -/
@[stacks 0FPH "ringed-site derived tensor localization"]
abbrev localization :
    (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf J O) ×
        ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf J O)) ⥤
      (ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O) ×
        ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.localization
    (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf J O))

/-- The two-variable total left-derived tensor functor for module sheaves. -/
@[stacks 0FPH "ringed-site derived tensor bifunctor"]
noncomputable abbrev functor [Has O] :
    (ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O) ×
        ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) ⥤
      ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O) :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.functor
    (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf J O))

/-- The two-variable derived tensor product of module-derived objects. -/
@[stacks 0FPH "ringed-site derived tensor object"]
noncomputable abbrev obj
    (K L : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) [Has O] :
    ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O) :=
  (functor O).obj (K, L)

/-- The bifunctorial counit from derived tensor to ordinary totalized tensor of module
homotopy objects. -/
@[stacks 0FPH "ringed-site derived tensor counit"]
noncomputable abbrev counit [Has O] :
    localization O ⋙ functor O ⟶ sourceFunctor O :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.counit
    (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf J O))

/-- Transport the canonical derived-tensor counit to an isomorphic module-derived tensor
model. -/
@[stacks 0FPH "ringed-site derived tensor transported counit"]
noncomputable abbrev counitOfIso [Has O]
    (T : (ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O) ×
          ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) ⥤
        ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O))
    (e : functor O ≅ T) :
    localization O ⋙ T ⟶ sourceFunctor O :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.counitOfIso T e

/-- The canonical isomorphism from total-left-derived tensor to any supplied two-variable
left-derived tensor model. -/
@[stacks 0FPH "ringed-site derived tensor model isomorphism"]
noncomputable abbrev modelIso [Has O]
    (T : (ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O) ×
          ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) ⥤
        ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O))
    (ε : localization O ⋙ T ⟶ sourceFunctor O)
    [T.IsLeftDerivedFunctor ε (qis O)] :
    functor O ≅ T :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.modelIso T ε

/-- The canonical module-derived model isomorphism identifies the transported counit with the
supplied one. -/
@[stacks 0FPH "ringed-site derived tensor model counit"]
theorem counitOfIso_modelIso [Has O]
    (T : (ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O) ×
          ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) ⥤
        ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O))
    (ε : localization O ⋙ T ⟶ sourceFunctor O)
    [T.IsLeftDerivedFunctor ε (qis O)] :
    counitOfIso O T (modelIso O T ε) = ε := sorry

end RingedSite.Hom.ModuleDerived.Tensor
