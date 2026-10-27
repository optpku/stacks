/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.FlatLift.IsoClass
public import ReasLib.CategoryTheory.Abelian.Extension.Classification
import StacksCheckRecall

/-!
# Isomorphism classes of flat lifts across a strict morphism of first-order thickenings

On a morphism of first-order thickenings as in Situation 91.9.1, if `(f, f')` is strict
and `F` is flat over `O_B`, then existence of one flat lift implies that isomorphism
classes of flat lifts form a principal homogeneous space under `Ext F (I ⊗_O F) 1`.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.ChangeOfRings
open SheafOfModules.RingedSite
open CategoryTheory.Abelian (Ext)

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace FlatLift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable {OB' OB O' O : Sheaf J CommRingCat.{max u v}}
variable (π : O' ⟶ O) {τ : OB' ⟶ OB}
variable [IsFirstOrderThickening π] [IsFirstOrderThickening τ]
variable [(restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable (f : OB ⟶ O) [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
variable (f' : OB' ⟶ O') (hcomm : f' ≫ π = τ ≫ f)
variable (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J O)
variable [IsFlat OB ((restrictionAlong f).obj F)]
variable [HasExt.{w} (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]

/- Lemma 91.11.7: Let `(f, f')` be a morphism of first-order thickenings as in
Situation 91.9.1. Let `F` be an `O`-module. Assume `(f, f')` is a strict morphism of
thickenings and `F` is flat over `O_B`. If there exists a pair `(F', α)` consisting of
an `O'`-module `F'` flat over `O_{B'}` and an isomorphism `α : i^* F' ⟶ F`, then the
set of isomorphism classes of such pairs is principal homogeneous under
`Ext F (moduleTensor (ideal π) F) 1`.

The Baer-sum action has unique translation between any two lift classes. Its
extension-class group is canonically identified with this Ext¹ group by the
additive bijection `ExtensionClass.toExt`, checked below. Together with
`vadd_zero` and `vadd_add`, unique translation expresses principal homogeneity. -/
@[stacks 08MU] #check
  (SheafOfModules.RingedSite.FirstOrderThickening.FlatLift.existsUnique_vadd :
    ∀ (hstrict : IsStrict f f' hcomm) (h_exists : Nonempty (FlatLift π f' F))
      (E E' : IsoClass π f' F),
      ∃! ξ : ExtensionClass (moduleTensor (ideal π) F) F, vadd hstrict ξ E = E')

/- The canonical comparison with Ext¹ is additive. -/
#check (CategoryTheory.ExtensionClass.toExtAddHom :
  ExtensionClass (moduleTensor (ideal π) F) F →+ Ext F (moduleTensor (ideal π) F) 1)

/- The same canonical comparison with Ext¹ is bijective. -/
#check (CategoryTheory.ExtensionClass.toExt_bijective :
  Function.Bijective (CategoryTheory.ExtensionClass.toExt :
    ExtensionClass (moduleTensor (ideal π) F) F → Ext F (moduleTensor (ideal π) F) 1))

end FlatLift
end SheafOfModules.RingedSite.FirstOrderThickening
