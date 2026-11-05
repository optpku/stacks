module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Scalar structures on sections over a ringed site

A morphism of commutative ring sheaves induces algebra and restricted-module structures on every
section object.  The morphism remains explicit: two fixed ring sheaves can admit several
structure morphisms, so these structures are not coherent global instances.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O₁ O₂ : Sheaf J CommRingCat.{w}}

/-- The `O₁(X)`-algebra structure on `O₂(X)` induced by a morphism of commutative ring sheaves. -/
@[stacks 0G3T "section scalar algebra"]
abbrev sectionAlgebra (φ : O₁ ⟶ O₂) (X : Cᵒᵖ) :
    Algebra (O₁.obj.obj X) (O₂.obj.obj X) :=
  (φ.hom.app X).hom.toAlgebra

/-- The `O₁(X)`-module structure on the sections `F(X)` obtained by restricting scalars along
`φ`. -/
@[stacks 0G3T "section scalar module"]
abbrev sectionModule (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (X : Cᵒᵖ) :
    Module (O₁.obj.obj X) (F.val.obj X) :=
  Module.compHom (F.val.obj X) (φ.hom.app X).hom

/-- The restricted module structure on a section, expressed through the underlying `RingCat`-
valued sheaf used by `SheafOfModules`. -/
@[stacks 0G3T "underlying-ring section scalar module"]
abbrev ringSectionModule
    (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (X : Cᵒᵖ) :
    Module ((ringSheaf J O₁).obj.obj X) (F.val.obj X) :=
  Module.compHom (F.val.obj X) ((ringSheafMap φ).hom.app X).hom

/-- The sectionwise scalar-tower law for restriction along `φ`. -/
@[stacks 0G3T "section scalar tower"]
theorem sectionIsScalarTower (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (X : Cᵒᵖ) :
    @IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X)
      (sectionAlgebra φ X).toSMul (F.val.obj X).isModule.toSMul
      (sectionModule φ F X).toSMul := sorry

end SheafOfModules.RingedSite


