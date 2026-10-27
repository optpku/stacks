/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Equivalence
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Module sheaves on ringed sites

This module owns the ordinary category of module sheaves on an arbitrary ringed site.  Derived
categories and derived functors belong in the sibling `Derived` hierarchy.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite (ringedSiteModuleCategory)

noncomputable section

namespace RingedSite

/-- The abelian category of sheaves of modules on a ringed site. -/
@[stacks 03CW "intrinsic ringed-site module category"]
abbrev ModuleCat.{z, u, v, w} (X : RingedSite.{u, v, w}) :=
  SheafOfModules.{z} X.structureSheaf

universe u v w z

namespace RingPresentation
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (O : Sheaf J RingCat.{w}) [UnivLE.{max u v, z}]

/-- The canonical abelian structure on modules over a ring-sheaf presentation.  This direct
presentation instance lets typeclass search use a ring sheaf without reconstructing its bundled
ringed site. -/
@[stacks 03CW "ringed-site abelian presentation"]
noncomputable instance moduleAbelian :
    Abelian (SheafOfModules.{z} O) := by
  -- Local instance justification (proof-local temporary data): UnivLE transports filtered-colimit preservation to the section universe required by the canonical plus construction.
  letI : Limits.PreservesFilteredColimitsOfSize.{max u v, max u v}
      (forget AddCommGrpCat.{z}) :=
    Limits.preservesFilteredColimitsOfSize_of_univLE (forget AddCommGrpCat.{z})
  -- Local instance justification (proof-local temporary data): the preceding filtered-colimit transport supplies canonical additive sheafification in section universe z.
  letI : HasSheafify J AddCommGrpCat.{z} := inferInstance
  -- Local instance justification (proof-local temporary data): UnivLE makes the site objects small in the section universe needed to construct the canonical small-model equivalence.
  letI : Small.{z} C :=
    @Small.trans_univLE.{max u v, z, u} C (small_max.{v} C) inferInstance
  -- Local instance justification (proof-local temporary data): UnivLE transports each hom-set to section universe z so the canonical small-model equivalence has the required locally small category.
  letI : LocallySmall.{z} C :=
    ⟨fun U V => @Small.trans_univLE.{max u v, z, v} (U ⟶ V)
      (small_max.{u} (U ⟶ V)) inferInstance⟩
  -- Local instance justification (proof-local temporary data): object and hom smallness supply the small-model owner used by the sheafification and locally-bijective comparison.
  letI : EssentiallySmall.{z} C := inferInstance
  -- Local instance justification (proof-local temporary data): the small-model equivalence gives small structured-arrow indexing categories for pointwise transport in section universe z.
  letI : ∀ V : Cᵒᵖ,
      Small.{z} (StructuredArrow V (equivSmallModel C).inverse.op) :=
    fun _ => inferInstance
  -- Local instance justification (proof-local temporary data): these small structured-arrow categories admit the additive limits needed for canonical sheafification transport along the small-model equivalence.
  letI : ∀ V : Cᵒᵖ,
      Limits.HasLimitsOfShape (StructuredArrow V (equivSmallModel C).inverse.op)
        AddCommGrpCat.{z} := fun _ => inferInstance
  -- Local instance justification (proof-local temporary data): canonical sheafification on the small model identifies its inverted maps with locally bijective maps, as required by module-sheaf abelianness.
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{z} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J
  exact SheafOfModules.instAbelian O

/-- Finite biproducts on modules over a ring-sheaf presentation. -/
@[stacks 03CW "ringed-site finite biproducts"]
noncomputable instance moduleHasFiniteBiproducts :
    Limits.HasFiniteBiproducts (SheafOfModules.{z} O) :=
  Abelian.hasFiniteBiproducts

end RingPresentation

namespace CommRingPresentation
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable (O : Sheaf J CommRingCat.{w}) [UnivLE.{max u v, z}]

/-- The canonical abelian structure on modules over a commutative ring-sheaf presentation. This
specialization lets typeclass search recognize the presentation without unfolding the bundled
ringed site. -/
@[stacks 03CW "commutative ringed-site abelian presentation"]
noncomputable instance moduleAbelian :
    Abelian (ringedSiteModuleCategory.{u, v, z, w} J O) :=
  RingPresentation.moduleAbelian J (CategoryTheory.Sheaf.ringSheafOfComm O)

/-- Finite biproducts on modules over a commutative ring-sheaf presentation. -/
@[stacks 03CW "commutative ringed-site finite biproducts"]
noncomputable instance moduleHasFiniteBiproducts :
    Limits.HasFiniteBiproducts (ringedSiteModuleCategory.{u, v, z, w} J O) :=
  Abelian.hasFiniteBiproducts

end CommRingPresentation
namespace CommRingPresentation
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable (O : Sheaf J CommRingCat.{max u v})
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The commutative-ring presentation of a ringed site inherits the canonical Grothendieck
abelian structure of sheaves of modules.  This bridge keeps derived RHom typeclass search from
having to unfold `ofCommRingSheaf` and `ringedSiteModuleCategory` at every use site. -/
@[stacks 0142 "commutative ringed-site Grothendieck owner"]
noncomputable instance moduleIsGrothendieckAbelian :
    IsGrothendieckAbelian.{max u v}
      (ringedSiteModuleCategory.{u, v, max u v, max u v} J O) :=
  SheafOfModules.isGrothendieckAbelian (CategoryTheory.Sheaf.ringSheafOfComm O)

end CommRingPresentation

/-- The module category of a ringed site is abelian. -/
abbrev moduleCatAbelian.{zM, uC, vC, wR}
    (X : RingedSite.{uC, vC, wR}) [UnivLE.{max uC vC, zM}] :
    Abelian (ModuleCat.{zM} X) :=
  RingPresentation.moduleAbelian X.siteTopology X.structureSheaf

/-- Finite biproducts for bundled ringed-site module categories are derived from the canonical
abelian owner and are shared by homological-complex and derived-category APIs. -/
@[stacks 03CW "finite biproducts of ringed-site modules"]
noncomputable abbrev moduleCatHasFiniteBiproducts.{zM, uC, vC, wR}
    (X : RingedSite.{uC, vC, wR}) [UnivLE.{max uC vC, zM}] :
    Limits.HasFiniteBiproducts (ModuleCat.{zM} X) :=
  Abelian.hasFiniteBiproducts

end RingedSite
-- Products, kernels and cokernels above use the native module-sheaf constructions.
-- Their existence witnesses contain the actual objects and maps.
