module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PresheafMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Sheafification of pointwise tensor products

This file owns the concrete object obtained by tensoring two module presheaves pointwise and then
sheafifying.  It is independent of the monoidal-localization construction on module sheaves and
therefore serves as its bootstrap presentation as well as a reusable target for presheaf-level
bilinear constructions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ModuleSheafification

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})

/-- The bifunctor which tensors two module presheaves pointwise and then sheafifies. -/
@[stacks 03L6 "sheafified pointwise tensor bifunctor"]
noncomputable def tensorFunctor :
    PresheafOfModules (ringSheaf J O).obj ⥤
      PresheafOfModules (ringSheaf J O).obj ⥤ ringedSiteModuleCategory J O :=
  (Functor.postcompose₂.obj (moduleSheafification O)).obj
    (MonoidalCategory.curriedTensor _)

/-- Sheafification of the pointwise tensor product of two module presheaves. -/
@[stacks 03L6 "sheafification of a pointwise module-presheaf tensor product"]
noncomputable abbrev tensorObj
    (P Q : PresheafOfModules (ringSheaf J O).obj) : ringedSiteModuleCategory J O :=
  ((tensorFunctor O).obj P).obj Q

/-- The morphism between sheafified pointwise tensor products induced in the two factors. -/
@[stacks 03L6 "maps between sheafified pointwise tensor products"]
noncomputable def tensorMap
    {P₁ P₂ Q₁ Q₂ : PresheafOfModules (ringSheaf J O).obj}
    (f : P₁ ⟶ P₂) (g : Q₁ ⟶ Q₂) :
    tensorObj O P₁ Q₁ ⟶ tensorObj O P₂ Q₂ :=
  ((tensorFunctor O).map f).app Q₁ ≫ ((tensorFunctor O).obj P₂).map g

/-- The sheafified pointwise tensor map preserves identity morphisms. -/
@[simp, stacks 03L6 "identity law for sheafified tensor maps"]
theorem tensorMap_id (P Q : PresheafOfModules (ringSheaf J O).obj) :
    tensorMap O (𝟙 P) (𝟙 Q) = 𝟙 (tensorObj O P Q) := sorry

/-- The sheafified pointwise tensor map preserves composition in both variables. -/
@[stacks 03L6 "composition law for sheafified tensor maps"]
theorem tensorMap_comp
    {P₁ P₂ P₃ Q₁ Q₂ Q₃ : PresheafOfModules (ringSheaf J O).obj}
    (f : P₁ ⟶ P₂) (f' : P₂ ⟶ P₃) (g : Q₁ ⟶ Q₂) (g' : Q₂ ⟶ Q₃) :
    tensorMap O (f ≫ f') (g ≫ g') =
      tensorMap O f g ≫ tensorMap O f' g' := sorry

/-- The sheafification unit from a pointwise tensor presheaf to the underlying presheaf of its
sheafification. -/
@[stacks 03L6 "unit for a sheafified pointwise tensor product"]
noncomputable def tensorUnitToVal
    (P Q : PresheafOfModules (ringSheaf J O).obj) :
    PresheafOfModules.Monoidal.tensorObj P Q ⟶ (tensorObj O P Q).val :=
  moduleSheafificationUnitToVal O _

/-- The sheafification adjunction identifies maps out of a sheafified pointwise tensor with maps
from the pointwise tensor presheaf. -/
@[stacks 03L6 "Hom equivalence for a sheafified tensor product"]
noncomputable def tensorHomEquiv
    {P Q : PresheafOfModules (ringSheaf J O).obj}
    (H : ringedSiteModuleCategory J O) :
    (tensorObj O P Q ⟶ H) ≃
      (PresheafOfModules.Monoidal.tensorObj P Q ⟶ H.val) :=
  moduleSheafificationHomEquiv O _ H

/-- Under `tensorHomEquiv`, a sheaf morphism is represented by its underlying morphism after the
sheafification unit. -/
@[stacks 03L6 "forward map of the sheafified tensor Hom equivalence"]
theorem tensorHomEquiv_apply
    {P Q : PresheafOfModules (ringSheaf J O).obj}
    (H : ringedSiteModuleCategory J O) (f : tensorObj O P Q ⟶ H) :
    tensorHomEquiv O H f = tensorUnitToVal O P Q ≫ f.val := sorry

/-- Descend an explicitly supplied morphism from a pointwise tensor presheaf to a module sheaf. -/
@[stacks 03L6 "descent from a pointwise tensor presheaf"]
noncomputable def tensorLift
    {P Q : PresheafOfModules (ringSheaf J O).obj}
    (H : ringedSiteModuleCategory J O)
    (f : PresheafOfModules.Monoidal.tensorObj P Q ⟶ H.val) :
    tensorObj O P Q ⟶ H :=
  (tensorHomEquiv O H).symm f

/-- A descended tensor-presheaf morphism recovers the supplied morphism after the sheafification
unit. -/
@[reassoc, stacks 03L6 "descent equation for a sheafified tensor product"]
theorem tensorLift_unitToVal
    {P Q : PresheafOfModules (ringSheaf J O).obj}
    (H : ringedSiteModuleCategory J O)
    (f : PresheafOfModules.Monoidal.tensorObj P Q ⟶ H.val) :
    tensorUnitToVal O P Q ≫ (tensorLift O H f).val = f := sorry

/-- Morphisms from a sheafified pointwise tensor are determined after precomposition with the
sheafification unit. -/
@[ext, stacks 03L6 "extensionality for sheafified tensor morphisms"]
theorem tensorHom_ext
    {P Q : PresheafOfModules (ringSheaf J O).obj}
    {H : ringedSiteModuleCategory J O} {f g : tensorObj O P Q ⟶ H}
    (h : tensorUnitToVal O P Q ≫ f.val = tensorUnitToVal O P Q ≫ g.val) :
    f = g := sorry

/-- Naturality of the sheafification unit for a pointwise tensor of module-presheaf maps. -/
@[reassoc, stacks 03L6 "naturality of the sheafified tensor unit"]
theorem tensorMap_unitToVal
    {P₁ P₂ Q₁ Q₂ : PresheafOfModules (ringSheaf J O).obj}
    (f : P₁ ⟶ P₂) (g : Q₁ ⟶ Q₂) :
    PresheafOfModules.Monoidal.tensorHom f g ≫ tensorUnitToVal O P₂ Q₂ =
      tensorUnitToVal O P₁ Q₁ ≫ (tensorMap O f g).val := sorry



end SheafOfModules.RingedSite.ModuleSheafification
