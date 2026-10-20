/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
import StacksCheckRecall

/-!
# Lemma 18.27.8 compatibility facade

The source is the restriction–coextension adjunction, not the
extension–restriction adjunction.  The reusable owner accepts an explicit coextension functor
and its adjunction, so the Hom equivalence does not depend on an existentially chosen right
adjoint.

The remaining construction boundary is intentional: the current module-sheaf monoidal API has
no equivalence between native `𝒪'`-module sheaves and internal modules over
`(restrictionAlong α).obj (unitModule J 𝒪')` in the monoidal category of `𝒪`-module
sheaves.  Consequently this facade does not claim that an abstract `ihom` has already been
re-bundled with its canonical `𝒪'`-action.  Here `H` is explicit data for that coextension
model and `adj` is its universal-property witness.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪')
variable (H : ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory J 𝒪')
variable (adj : restrictionAlong α ⊣ H)
variable (G : ringedSiteModuleCategory J 𝒪') (F : ringedSiteModuleCategory J 𝒪)

/- Lemma 18.27.8 (0932): for an explicitly supplied coextension model `H` of restriction along
`α : 𝒪 ⟶ 𝒪'`, an `𝒪'`-module `G`, and an `𝒪`-module `F`, restriction–coextension
adjunction gives
`Hom_𝒪((restrictionAlong α).obj G, F) ≃ Hom_𝒪'(G, H.obj F)`.

When the missing native/internal-module bridge is supplied, `H.obj F` is the `𝒪'`-module
customarily denoted `Hom_𝒪(𝒪', F)`. -/
@[stacks 0932]
#check
  (Coextension.homEquiv α H adj G F :
    ((restrictionAlong α).obj G ⟶ F) ≃ (G ⟶ H.obj F))

/- The reusable owner also records both unit/counit formulas and naturality in the two module
variables. -/
#check @Coextension.homEquiv_apply
#check @Coextension.homEquiv_symm_apply
#check @Coextension.homEquiv_naturality_source
#check @Coextension.homEquiv_naturality_target

/- For callers that already have a genuine `Functor.IsLeftAdjoint` instance, the chosen
right-adjoint convenience layer has the same correctly oriented Hom equivalence. -/
#check @coextendAlong.homEquiv
