module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Derived.LocalizationAway
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u v w z

namespace RingedSite.Hom.ModuleDerived.LocalizationAway

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, z}]

/-- A local section is localization-away vanishing for `K` when a homotopy-limit
representative of its multiplication tower exists and is zero. -/
def IsVanishingAt
    (K : SheafOfModules.LocalizationAway.Derived.{u, v, w, z} O)
    (U : Cᵒᵖ) (f : O.obj.obj U) : Prop :=
  ∃ T : SheafOfModules.LocalizationAway.Derived.{max u v, v, w, z} (O.over U.unop),
    HomotopyLimit.IsOf
      (SheafOfModules.LocalizationAway.tower K U.unop f) T ∧ IsZero T

namespace IsVanishingAt

/-- Every homotopy-limit representative of a localization-away vanishing tower is zero. -/
theorem isZero
    {K : SheafOfModules.LocalizationAway.Derived.{u, v, w, z} O}
    {U : Cᵒᵖ} {f : O.obj.obj U} (hf : IsVanishingAt K U f)
    {T : SheafOfModules.LocalizationAway.Derived.{max u v, v, w, z} (O.over U.unop)}
    (hT : HomotopyLimit.IsOf
      (SheafOfModules.LocalizationAway.tower K U.unop f) T) : IsZero T := sorry

/-- The zero local section is localization-away vanishing. -/
theorem zero
    (K : SheafOfModules.LocalizationAway.Derived.{u, v, w, z} O) (U : Cᵒᵖ) :
    IsVanishingAt K U 0 := sorry

/-- The sum of localization-away vanishing local sections is localization-away vanishing. -/
theorem add
    (K : SheafOfModules.LocalizationAway.Derived.{u, v, w, z} O) {U : Cᵒᵖ}
    {f g : O.obj.obj U} (hf : IsVanishingAt K U f) (hg : IsVanishingAt K U g) :
    IsVanishingAt K U (f + g) := sorry

/-- Multiplying a localization-away vanishing section by a local section preserves
localization-away vanishing. -/
theorem mul_left
    (K : SheafOfModules.LocalizationAway.Derived.{u, v, w, z} O) {U : Cᵒᵖ}
    (g : O.obj.obj U) {f : O.obj.obj U} (hf : IsVanishingAt K U f) :
    IsVanishingAt K U (g * f) := sorry

/-- Restriction of a localization-away vanishing section is localization-away vanishing. -/
theorem map
    (K : SheafOfModules.LocalizationAway.Derived.{u, v, w, z} O) {U V : Cᵒᵖ}
    (g : U ⟶ V) {f : O.obj.obj U} (hf : IsVanishingAt K U f) :
    IsVanishingAt K V (O.obj.map g f) := sorry

end IsVanishingAt

/-- The restriction-stable presheaf submodule of localization-away vanishing sections. -/
noncomputable def presheafSubmodule
    (K : SheafOfModules.LocalizationAway.Derived.{u, v, w, z} O) :
    PresheafOfModules.Submodule (unitModule J O).val where
  obj U :=
    { carrier := fun f ↦ IsVanishingAt K U f
      zero_mem' := IsVanishingAt.zero K U
      add_mem' := fun hf hg ↦ hf.add K hg
      smul_mem' := fun g _ hf ↦ hf.mul_left K g }
  map g _ hf := hf.map K g

/-- Membership in the vanishing presheaf submodule is localization-away vanishing. -/
theorem mem_presheafSubmodule_iff
    (K : SheafOfModules.LocalizationAway.Derived.{u, v, w, z} O)
    (U : Cᵒᵖ) (f : O.obj.obj U) :
    f ∈ (presheafSubmodule K).obj U ↔ IsVanishingAt K U f := sorry

/-- The presheaf of localization-away vanishing sections satisfies the sheaf condition. -/
theorem presheafSubmodule_isSheaf
    (K : SheafOfModules.LocalizationAway.Derived.{u, v, w, z} O) :
    Presheaf.IsSheaf J (presheafSubmodule K).toPresheafOfModules.presheaf := sorry

/-- The ideal sheaf of local sections whose localization-away tower for `K` has zero
homotopy limit. -/
noncomputable def ideal
    (K : SheafOfModules.LocalizationAway.Derived.{u, v, w, z} O) :
    Subobject (unitModule J O) :=
  let N := presheafSubmodule K
  let I : ringedSiteModuleCategory J O :=
    { val := N.toPresheafOfModules
      isSheaf := presheafSubmodule_isSheaf K }
  let i : I ⟶ unitModule J O := { val := N.ι }
  @Subobject.mk _ _ _ _ i
    ((SheafOfModules.forget (ringSheaf J O)).mono_of_mono_map
      (inferInstance : Mono N.ι))

/-- The section ideal of `ideal K` is the objectwise vanishing submodule. -/
theorem ideal_sections
    (K : SheafOfModules.LocalizationAway.Derived.{u, v, w, z} O) (U : Cᵒᵖ) :
    IdealSheaf.sections (ideal K) U = (presheafSubmodule K).obj U := sorry

/-- Membership in the ideal sheaf of vanishing sections is equivalent to vanishing of
the localization-away homotopy limit. -/
theorem mem_ideal_iff
    (K : SheafOfModules.LocalizationAway.Derived.{u, v, w, z} O)
    (U : Cᵒᵖ) (f : O.obj.obj U) :
    f ∈ IdealSheaf.sections (ideal K) U ↔ IsVanishingAt K U f := sorry

end RingedSite.Hom.ModuleDerived.LocalizationAway
