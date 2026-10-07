module

public import Mathlib.Algebra.Homology.Additive
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Action.HomologicalComplex
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.CategoryTheory.Monoidal.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ideal-sheaf actions and invertible tensor factors

The action of an ideal sheaf on `M ⊗ L` is the action on `M`, tensored on the right by `L`,
after reassociation.  Consequently, tensoring by an invertible module preserves and reflects
monicity of the action, both for modules and degreewise for homological complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v w z

namespace SheafOfModules.RingedSite.IdealSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}}

/-- The ideal action on `M ⊗ L` is the ideal action on `M`, tensored by `L`, after the
canonical reassociation.  This identity does not require `L` to be invertible. -/
@[reassoc, stacks 0F9W "ideal action and right tensor"]
theorem action_tensorRight
    (I : Subobject (unitModule J O))
    (M L : ringedSiteModuleCategory.{u, v, w, w} J O) :
    (α_ (I : ringedSiteModuleCategory J O) M L).hom ≫
        action I ((tensorRight L).obj M) =
      (tensorRight L).map (action I M) := sorry

namespace IsActionMono

/-- Tensoring on the right by an invertible module reflects and preserves monicity of an
ideal-sheaf action. -/
@[stacks 0F9W "module-level tensor invariance"]
theorem tensorRight_iff
    (I : Subobject (unitModule J O))
    (M L : ringedSiteModuleCategory.{u, v, w, w} J O)
    [isInvertibleObject L] :
    IsActionMono I ((tensorRight L).obj M) ↔ IsActionMono I M := sorry

/-- Tensoring a module with monic ideal action on the right by a flat module again has monic
ideal action. -/
@[stacks 0F9W "module-level tensor preservation", instance]
theorem tensorRight
    (I : Subobject (unitModule J O))
    (M L : ringedSiteModuleCategory.{u, v, w, w} J O)
    [IsFlat L] [IsActionMono I M] :
    IsActionMono I ((tensorRight L).obj M) := sorry

namespace Complex

variable {i : Type z}

/-- Degreewise monicity of an ideal action is invariant under termwise right tensoring by an
invertible module. -/
@[stacks 0F9W "complex-level tensor invariance"]
theorem tensorRight_iff
    (I : Subobject (unitModule J O)) (c : ComplexShape i)
    (K : HomologicalComplex (ringedSiteModuleCategory.{u, v, w, w} J O) c)
    (L : ringedSiteModuleCategory.{u, v, w, w} J O)
    [isInvertibleObject L] :
    Complex I (((MonoidalCategory.tensorRight L).mapHomologicalComplex c).obj K) ↔
      Complex I K := sorry

/-- Termwise right tensoring by a flat module preserves degreewise monicity of an ideal-sheaf
action. -/
@[stacks 0F9W "complex-level tensor preservation", instance]
theorem tensorRight
    (I : Subobject (unitModule J O)) (c : ComplexShape i)
    (K : HomologicalComplex (ringedSiteModuleCategory.{u, v, w, w} J O) c)
    (L : ringedSiteModuleCategory.{u, v, w, w} J O)
    [IsFlat L] [Complex I K] :
    Complex I (((MonoidalCategory.tensorRight L).mapHomologicalComplex c).obj K) := sorry

end Complex

end IsActionMono

end SheafOfModules.RingedSite.IdealSheaf
