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
  _root_.SheafOfModules.{z} X.structureSheaf

/-- The module category of a ringed site is abelian. -/
instance moduleCatAbelian.{z, u, v, w}
    (X : RingedSite.{u, v, w}) [UnivLE.{max u v, z}] :
    Abelian (ModuleCat.{z} X) := by
  -- The supplied site-size bound permits the native plus construction at section universe `z`.
  letI : Limits.PreservesFilteredColimitsOfSize.{max u v, max u v}
      (forget AddCommGrpCat.{z}) :=
    Limits.preservesFilteredColimitsOfSize_of_univLE (forget AddCommGrpCat.{z})
  letI : HasSheafify X.siteTopology AddCommGrpCat.{z} := inferInstance
  -- A genuine small site model transports the native local-bijectivity law.
  letI : Small.{z} X.carrier :=
    @Small.trans_univLE.{max u v, z, u} X.carrier (small_max.{v} X.carrier) inferInstance
  letI : LocallySmall.{z} X.carrier :=
    ⟨fun U V => @Small.trans_univLE.{max u v, z, v} (U ⟶ V)
      (small_max.{u} (U ⟶ V)) inferInstance⟩
  letI : EssentiallySmall.{z} X.carrier := inferInstance
  letI : ∀ V : X.carrierᵒᵖ,
      Small.{z} (StructuredArrow V (equivSmallModel X.carrier).inverse.op) :=
    fun _ => inferInstance
  letI : ∀ V : X.carrierᵒᵖ,
      Limits.HasLimitsOfShape (StructuredArrow V (equivSmallModel X.carrier).inverse.op)
        AddCommGrpCat.{z} := fun _ => inferInstance
  letI : X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall X.siteTopology
  exact SheafOfModules.instAbelian X.structureSheaf

/-- Finite biproducts for bundled ringed-site module categories are derived from the canonical
abelian owner and are shared by homological-complex and derived-category APIs. -/
@[stacks 03CW "finite biproducts of ringed-site modules"]
noncomputable instance moduleCatHasFiniteBiproducts.{z, u, v, w}
    (X : RingedSite.{u, v, w}) [UnivLE.{max u v, z}] :
    Limits.HasFiniteBiproducts (ModuleCat.{z} X) :=
  Abelian.hasFiniteBiproducts

end RingedSite

universe u v w z

namespace RingedSite.RingPresentation

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (O : Sheaf J RingCat.{w}) [UnivLE.{max u v, z}]

/-- The canonical abelian structure on modules over a ring-sheaf presentation.  This direct
presentation instance lets typeclass search use a ring sheaf without reconstructing its bundled
ringed site. -/
@[stacks 03CW "ringed-site abelian presentation"]
noncomputable instance moduleAbelian :
    Abelian (SheafOfModules.{z} O) :=
  RingedSite.moduleCatAbelian (RingedSite.ofRingSheaf J O)

/-- Finite biproducts on modules over a ring-sheaf presentation. -/
@[stacks 03CW "ringed-site finite biproducts"]
noncomputable instance moduleHasFiniteBiproducts :
    Limits.HasFiniteBiproducts (SheafOfModules.{z} O) :=
  Abelian.hasFiniteBiproducts

end RingedSite.RingPresentation

namespace RingedSite.CommRingPresentation

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable (O : Sheaf J CommRingCat.{w}) [UnivLE.{max u v, z}]

/-- The canonical abelian structure on modules over a commutative ring-sheaf presentation. This
specialization lets typeclass search recognize the presentation without unfolding the bundled
ringed site. -/
@[stacks 03CW "commutative ringed-site abelian presentation"]
noncomputable instance moduleAbelian :
    Abelian (ringedSiteModuleCategory.{u, v, z, w} J O) :=
  RingedSite.moduleCatAbelian (RingedSite.ofCommRingSheaf J O)

/-- Finite biproducts on modules over a commutative ring-sheaf presentation. -/
@[stacks 03CW "commutative ringed-site finite biproducts"]
noncomputable instance moduleHasFiniteBiproducts :
    Limits.HasFiniteBiproducts (ringedSiteModuleCategory.{u, v, z, w} J O) :=
  Abelian.hasFiniteBiproducts

end RingedSite.CommRingPresentation

namespace RingedSite.CommRingPresentation

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

end RingedSite.CommRingPresentation


-- Products, kernels and cokernels above use the native module-sheaf constructions.
-- Their existence witnesses contain the actual objects and maps.
