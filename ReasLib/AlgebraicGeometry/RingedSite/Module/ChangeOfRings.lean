/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coextension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SameSiteTensorExtension
public import ReasLib.AlgebraicGeometry.RingedSite.Basic

/-!
# Change of rings on a ringed site

This module contains same-site change-of-rings constructions for sheaves of
modules. The site and its structure sheaves are arbitrary.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace RingedSite.SameSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {O O' : Sheaf J RingCat.{w}}

/-- A morphism of ring sheaves on one site, written in the adjoint structure-map orientation
required by a morphism of ringed sites. -/
@[stacks 03CZ "same-site ringed-site structure map"]
abbrev structureMap (α : O ⟶ O') :
    O ⟶ ((𝟭 C).sheafPushforwardContinuous RingCat.{w} J J).obj O' :=
  α ≫ (Functor.sheafPushforwardContinuousId RingCat.{w} J).inv.app O'

/-- The same-site morphism of ringed sites induced by a morphism of arbitrary ring sheaves. -/
@[stacks 03CZ "same-site morphism of ringed sites"]
abbrev hom (α : O ⟶ O') :
    RingedSite.ofRingSheaf J O' ⟶ RingedSite.ofRingSheaf J O where
  base := 𝟭 C
  isMorphismOfSites := inferInstance
  structureSheafMap := structureMap α



end RingedSite.SameSite

namespace SheafOfModules.RingedSite

/-- The same-site morphism of commutative ringed sites induced by a morphism of structure sheaves
on a fixed site. -/
@[stacks 03CZ "same-site commutative ringed-site morphism"]
abbrev sameSiteHom {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {𝒪 𝒪' : Sheaf J CommRingCat.{w}} (α : 𝒪 ⟶ 𝒪') :
    RingedSite.ofCommRingSheaf J 𝒪' ⟶ RingedSite.ofCommRingSheaf J 𝒪 where
  base := 𝟭 C
  isMorphismOfSites := inferInstance
  structureSheafMap := ringedSiteStructureMap α

section Extension

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O₀ O₁ O₂ : Sheaf J CommRingCat.{w}}

/-- Same-site scalar extension is pointwise tensor followed by sheafification;
its construction does not impose a small-category bound on the site. -/
def explicitExtendAlong (α : O₀ ⟶ O₁) :
    SheafOfModules.{w} (ringSheaf J O₀) ⥤ SheafOfModules.{w} (ringSheaf J O₁) := by
  let sh : PresheafOfModules.{w} (ringSheaf J O₁).obj ⥤
      SheafOfModules.{w} (ringSheaf J O₁) :=
    PresheafOfModules.sheafification (𝟙 (ringSheaf J O₁).obj)
  exact SheafOfModules.forget (ringSheaf J O₀) ⋙
    PresheafOfModules.SameSiteTensorExtension.functor α.hom ⋙ sh

/-- The explicit tensor/sheafification adjunction on independently-sized sites. -/
def explicitExtendRestrictAdj (α : O₀ ⟶ O₁) :
    explicitExtendAlong α ⊣ restrictionAlong.{u, v, w, w} α :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N ↦
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O₁).obj)).homEquiv _ _).trans
          ((PresheafOfModules.SameSiteTensorExtension.homEquiv α.hom M.val N.val).trans
            ((SheafOfModules.fullyFaithfulForget (ringSheaf J O₀)).homEquiv
              (Y := (restrictionAlong.{u, v, w, w} α).obj N)).symm)
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

instance restrictionAlong_isRightAdjoint (α : O₀ ⟶ O₁) :
    (restrictionAlong.{u, v, w, w} α).IsRightAdjoint :=
  (explicitExtendRestrictAdj α).isRightAdjoint

instance sameSitePushforward_isRightAdjoint (α : O₀ ⟶ O₁) :
    (SheafOfModules.pushforward.{w} (ringedSiteStructureMap α)).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (SheafOfModules.ChangeOfRings.pushforwardIso
    (ringSheafMap α)).symm

/-- Extension of scalars for module sheaves along a same-site morphism of commutative ring
sheaves. -/
@[stacks 03CZ "same-site extension of scalars"]
noncomputable abbrev extendAlong (alpha : O₀ ⟶ O₁) :
    ringedSiteModuleCategory.{u, v, w, w} J O₀ ⥤ ringedSiteModuleCategory.{u, v, w, w} J O₁ :=
  SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap alpha)

/-- Same-site extension of scalars is left adjoint to restriction of scalars. -/
@[stacks 03CZ "same-site extension-restriction adjunction"]
noncomputable def extendRestrictAdj (alpha : O₀ ⟶ O₁) :
    extendAlong alpha ⊣ restrictionAlong.{u, v, w, w} alpha :=
  SheafOfModules.ChangeOfRings.extendRestrictAdjunction (ringSheafMap alpha)

/-- The original same-site module-sheaf pullback construction is canonically extension of
scalars.  This is the compatibility bridge for APIs that were defined before `extendAlong`
became the public owner. -/
@[stacks 03CZ "same-site pullback as extension of scalars"]
noncomputable def pullbackExtendIso (alpha : O₀ ⟶ O₁) :
    SheafOfModules.pullback.{w} (ringedSiteStructureMap alpha) ≅ extendAlong alpha :=
  SheafOfModules.ChangeOfRings.pullbackIso (ringSheafMap alpha)

/-- Forgetting commutativity carries a composite of commutative ring-sheaf maps to the
composite of the underlying ring-sheaf maps. -/
theorem ringSheafMap_comp (alpha : O₀ ⟶ O₁) (beta : O₁ ⟶ O₂) :
    ringSheafMap (alpha ≫ beta) = ringSheafMap alpha ≫ ringSheafMap beta := sorry

/-- Forgetting commutativity carries the identity of a commutative ring sheaf to the identity
of its underlying ring sheaf. -/
theorem ringSheafMap_id (O : Sheaf J CommRingCat.{w}) :
    ringSheafMap (𝟙 O) = 𝟙 (ringSheaf J O) := sorry

/-- Extension of scalars along the identity ring-sheaf morphism is canonically isomorphic to
the identity functor. -/
noncomputable def extendIdIso (O : Sheaf J CommRingCat.{w}) :
    extendAlong (𝟙 O) ≅ Functor.id (ringedSiteModuleCategory.{u, v, w, w} J O) :=
  Adjunction.leftAdjointUniq (extendRestrictAdj (𝟙 O))
    ((Adjunction.id :
        Functor.id (ringedSiteModuleCategory.{u, v, w, w} J O) ⊣
          Functor.id (ringedSiteModuleCategory.{u, v, w, w} J O)).ofNatIsoRight
      (SheafOfModules.Restriction.idIso' (ringSheafMap (𝟙 O)) (ringSheafMap_id O)))

/-- Successive same-site extensions of scalars are canonically isomorphic to extension along
the composite ring-sheaf morphism. -/
noncomputable def extendCompIso (alpha : O₀ ⟶ O₁) (beta : O₁ ⟶ O₂) :
    extendAlong alpha ⋙ extendAlong beta ≅ extendAlong (alpha ≫ beta) :=
  Adjunction.leftAdjointUniq
    (((extendRestrictAdj alpha).comp (extendRestrictAdj beta)).ofNatIsoRight
      (SheafOfModules.Restriction.compIso'
        (ringSheafMap alpha) (ringSheafMap beta) (ringSheafMap (alpha ≫ beta))
        (ringSheafMap_comp alpha beta)))
    (extendRestrictAdj (alpha ≫ beta))

/-- Extension of scalars on cochain complexes along a same-site morphism of commutative ring
sheaves. -/
noncomputable abbrev extendComplex (alpha : O₀ ⟶ O₁) :
    CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O₀) ℤ ⥤
      CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O₁) ℤ :=
  (extendAlong alpha).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The complex-level comparison between the original same-site pullback construction and
extension of scalars. -/
@[stacks 03CZ "same-site pullback of complexes as extension of scalars"]
noncomputable def pullbackComplexExtendIso (alpha : O₀ ⟶ O₁) :
    (SheafOfModules.pullback.{w} (ringedSiteStructureMap alpha)).mapHomologicalComplex
        (ComplexShape.up ℤ) ≅
      extendComplex alpha :=
  NatIso.mapHomologicalComplex (pullbackExtendIso alpha) (ComplexShape.up ℤ)

/-- Successive extensions of cochain complexes are canonically isomorphic to extension along
the composite ring-sheaf morphism. -/
noncomputable def extendComplexCompIso (alpha : O₀ ⟶ O₁) (beta : O₁ ⟶ O₂) :
    extendComplex alpha ⋙ extendComplex beta ≅ extendComplex (alpha ≫ beta) :=
  Functor.mapHomologicalComplexCompIso (extendCompIso alpha beta) (ComplexShape.up ℤ)

/-- Extension of cochain complexes along the identity ring-sheaf morphism is canonically
isomorphic to the identity functor. -/
noncomputable def extendComplexIdIso (O : Sheaf J CommRingCat.{w}) :
    extendComplex (𝟙 O) ≅
      Functor.id (CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ) :=
  NatIso.mapHomologicalComplex (extendIdIso O) (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)



end Extension

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

namespace Coextension

/-- The restriction–coextension Hom equivalence associated to an explicitly
supplied right adjoint of same-site restriction of scalars.  This is the choice-free categorical
core with respect to adjoint selection: the coextension functor and its adjunction are data,
rather than being recovered from an existential `Functor.IsLeftAdjoint` witness. -/
@[stacks 0932 "restriction-coextension Hom equivalence"]
def homEquiv
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪')
    (H : ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory J 𝒪')
    (adj : restrictionAlong α ⊣ H)
    (G : ringedSiteModuleCategory J 𝒪') (F : ringedSiteModuleCategory J 𝒪) :
    ((restrictionAlong α).obj G ⟶ F) ≃ (G ⟶ H.obj F) :=
  adj.homEquiv G F

/-- The forward restriction–coextension correspondence is composition with the adjunction unit,
followed by the coextension of the given morphism. -/
theorem homEquiv_apply
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪')
    (H : ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory J 𝒪')
    (adj : restrictionAlong α ⊣ H)
    (G : ringedSiteModuleCategory J 𝒪') (F : ringedSiteModuleCategory J 𝒪)
    (f : (restrictionAlong α).obj G ⟶ F) :
    homEquiv α H adj G F f = adj.unit.app G ≫ H.map f := sorry

/-- The inverse restriction–coextension correspondence restricts a coextension morphism and then
composes with the adjunction counit. -/
theorem homEquiv_symm_apply
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪')
    (H : ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory J 𝒪')
    (adj : restrictionAlong α ⊣ H)
    (G : ringedSiteModuleCategory J 𝒪') (F : ringedSiteModuleCategory J 𝒪)
    (g : G ⟶ H.obj F) :
    (homEquiv α H adj G F).symm g =
      (restrictionAlong α).map g ≫ adj.counit.app F := sorry

/-- The restriction–coextension Hom equivalence is contravariantly natural in the
`𝒪'`-module. -/
theorem homEquiv_naturality_source
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪')
    (H : ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory J 𝒪')
    (adj : restrictionAlong α ⊣ H)
    {G' G : ringedSiteModuleCategory J 𝒪'} {F : ringedSiteModuleCategory J 𝒪}
    (g : G' ⟶ G) (f : (restrictionAlong α).obj G ⟶ F) :
    homEquiv α H adj G' F ((restrictionAlong α).map g ≫ f) =
      g ≫ homEquiv α H adj G F f := sorry

/-- The restriction–coextension Hom equivalence is covariantly natural in the `𝒪`-module. -/
theorem homEquiv_naturality_target
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪')
    (H : ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory J 𝒪')
    (adj : restrictionAlong α ⊣ H)
    {G : ringedSiteModuleCategory J 𝒪'} {F F' : ringedSiteModuleCategory J 𝒪}
    (f : (restrictionAlong α).obj G ⟶ F) (h : F ⟶ F') :
    homEquiv α H adj G F' (f ≫ h) =
      homEquiv α H adj G F f ≫ H.map h := sorry

end Coextension

namespace coextendAlong

/-- The restriction–coextension Hom equivalence for the canonical right adjoint selected by an
ambient `Functor.IsLeftAdjoint` instance.  Use `Coextension.homEquiv` when an explicit
coextension functor and adjunction are already available. -/
noncomputable abbrev homEquiv
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪')
    (G : ringedSiteModuleCategory J 𝒪') (F : ringedSiteModuleCategory J 𝒪) :
    ((restrictionAlong α).obj G ⟶ F) ≃
      (G ⟶ (coextendAlong α).obj F) :=
  Coextension.homEquiv α (coextendAlong α) (restrictionCoextendAdj α) G F

end coextendAlong

-- `Coextension.homEquiv` is the explicit, choice-free categorical core.  The convenience API
-- `coextendAlong` uses the canonical global `restrictionAlong_isLeftAdjoint` instance and hence
-- selects `Functor.rightAdjoint`; its data may depend on `Classical.choice`, while the deferred
-- existence theorem contributes proof debt only through the instance argument.

end

end SheafOfModules.RingedSite
