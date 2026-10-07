module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationBaseChange
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationMonoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products and restriction of scalars on a ringed site

The sectionwise lax-monoidal comparison for restriction of scalars descends through module
sheafification.  The resulting morphism is expressed against the ambient tensor products by the
canonical monoidal-sheafification comparison.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.Restriction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O O' : Sheaf J CommRingCat.{max u v}}

/-- The canonical tensor comparison for restriction of scalars between module sheaves. -/
@[stacks 03L6 "tensor comparison for restriction of scalars"]
noncomputable def tensorComparison (b : O ⟶ O')
    (F G : ringedSiteModuleCategory J O') :
    moduleTensor ((restrictionAlong b).obj F) ((restrictionAlong b).obj G) ⟶
      (restrictionAlong b).obj (moduleTensor F G) :=
  (ModuleSheafification.tensorObjIso O
      ((restrictionAlong b).obj F) ((restrictionAlong b).obj G)).hom ≫
    ModuleSheafification.mapToRestriction b
      (PresheafOfModules.Restriction.tensorComparison b.hom F.val G.val) ≫
    (restrictionAlong b).map (ModuleSheafification.tensorObjIso O' F G).inv

/-- The tensor comparison for restriction of scalars is natural in both module-sheaf
arguments. -/
@[stacks 03L6 "naturality of the restriction tensor comparison"]
theorem tensorComparison_naturality (b : O ⟶ O')
    {F₁ F₂ G₁ G₂ : ringedSiteModuleCategory J O'}
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) :
    moduleTensorMap ((restrictionAlong b).map f) ((restrictionAlong b).map g) ≫
        tensorComparison b F₂ G₂ =
      tensorComparison b F₁ G₁ ≫
        (restrictionAlong b).map (moduleTensorMap f g) := sorry

end SheafOfModules.RingedSite.Restriction
