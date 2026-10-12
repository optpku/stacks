/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Derivation

/-!
# The additive morphism underlying a relative derivation

A relative derivation determines a natural morphism between the underlying additive sheaves.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open scoped RelativeDerivation

noncomputable section

universe u v w

namespace SheafOfModules.RelativeDerivation

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable {O₁ O₂ : Sheaf J CommRingCat.{w}}
variable {M : SheafOfModules (ringSheaf J O₂)}

/-- Naturality of the additive maps underlying a relative derivation. -/
theorem additiveMap_naturality (phi : O₁ ⟶ O₂) (D : Der[phi ; M])
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    ((SheafOfModules.toSheaf (ringSheaf J O₂)).obj
          (unitModule J O₂)).obj.map f ≫ AddCommGrpCat.ofHom D.d =
      AddCommGrpCat.ofHom D.d ≫
        ((SheafOfModules.toSheaf (ringSheaf J O₂)).obj M).obj.map f := sorry

/-- The natural morphism of additive sheaves underlying a relative derivation. -/
def additiveMap (phi : O₁ ⟶ O₂) (D : Der[phi ; M]) :
    (SheafOfModules.toSheaf (ringSheaf J O₂)).obj (unitModule J O₂) ⟶
      (SheafOfModules.toSheaf (ringSheaf J O₂)).obj M :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom D.d
      naturality := fun {U V} f ↦ additiveMap_naturality phi D f }

/-- The underlying additive map of a relative derivation evaluates sectionwise as its
derivation map. -/
theorem additiveMap_apply (phi : O₁ ⟶ O₂) (D : Der[phi ; M])
    (U : Cᵒᵖ) (x : O₂.obj.obj U) :
    (additiveMap phi D).hom.app U x = D.d x := sorry

end SheafOfModules.RelativeDerivation
