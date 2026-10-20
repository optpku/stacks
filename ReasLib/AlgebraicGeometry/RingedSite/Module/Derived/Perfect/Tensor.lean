module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor

/-!
# Perfect derived tensor products on ringed sites

Perfect objects are stable under the derived tensor product over the commutative structure
sheaf. The ordinary tensor is fixed by the ring-sheaf presentation; only the existence of its
fixed-right derived functors is an explicit input.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open RingedSite (ModuleCat)
open RingedSite.Hom (ModuleDerived)
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v w

set_option checkBinderAnnotations false

namespace RingedSite.Hom.ModuleDerived

-- Local instance justification (defeq pin): generic derived-tensor APIs must align with the canonical RingedSite.Hom.ModuleDerived presentation.
attribute [local instance] HasDerivedCategory.standard
  RingedSite.Hom.moduleCat_hasDerivedCategory
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : RingedSite.ofCommRingSheaf J O,
  HasWeakSheafify ((RingedSite.ofCommRingSheaf J O).localization U).siteTopology
    AddCommGrpCat.{w}]
variable [∀ U : RingedSite.ofCommRingSheaf J O,
  ((RingedSite.ofCommRingSheaf J O).localization U).siteTopology.WEqualsLocallyBijective
    AddCommGrpCat.{w}]
variable [DerivedCategory.DerivedTensor.Right.Has
  (C := SheafOfModules.RingedSite.ringedSiteModuleCategory.{u, v, w, w} J O)]

/-- The derived tensor product of two perfect objects of `D(𝒪_X)` is perfect. -/
@[stacks 09JB]
theorem IsPerfect.tensor
    {K L : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)} (hK : K.IsPerfect) (hL : L.IsPerfect) :
    IsPerfect (K ⊗ᴸ L) := sorry

end

end RingedSite.Hom.ModuleDerived
