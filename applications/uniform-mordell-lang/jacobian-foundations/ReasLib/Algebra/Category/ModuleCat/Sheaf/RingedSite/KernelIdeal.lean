module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernel ideals on ringed sites

This file exposes the kernel of a same-site morphism of commutative ring sheaves at the three
levels used downstream: as a categorical subobject, as its sheaf of modules, and as the ordinary
ideal `RingHom.ker` on every object of the site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O₂ A : Sheaf J CommRingCat.{w}} (π : A ⟶ O₂)

namespace KernelIdeal

/-- The `A`-linear map whose categorical kernel is the kernel ideal of `π`. -/
abbrev map (π : A ⟶ O₂) :
    SheafOfModules.unit (ringSheaf J A) ⟶
      (SheafOfModules.pushforward (ringedSiteStructureMap π)).obj
        (SheafOfModules.unit (ringSheaf J O₂)) :=
  SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap π)

/-- The kernel ideal of `π` as a subobject of the unit `A`-module sheaf. -/
@[stacks 04BP "kernel ideal in Lemma 18.33.9"]
abbrev subobject (π : A ⟶ O₂) : Subobject (unitModule J A) :=
  kernelSubobject (map π)

/-- The sheaf of `A`-modules underlying the kernel ideal subobject. -/
abbrev sheaf (π : A ⟶ O₂) : SheafOfModules (ringSheaf J A) :=
  subobject π

/-- The canonical inclusion of the kernel ideal into the unit `A`-module sheaf. -/
abbrev ι (π : A ⟶ O₂) : sheaf π ⟶ unitModule J A :=
  (subobject π).arrow

section Underlying

variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

/-- The underlying additive sheaf of the kernel ideal is the categorical kernel of the
underlying additive map. -/
@[stacks 01UP "underlying additive kernel ideal",
  stacks 04BP "underlying additive kernel ideal"]
noncomputable def underlyingKernelIso (π : A ⟶ O₂) :
    (SheafOfModules.toSheaf (ringSheaf J A)).obj (sheaf π) ≅
      kernel ((SheafOfModules.toSheaf (ringSheaf J A)).map (map π)) :=
  (SheafOfModules.toSheaf (ringSheaf J A)).mapIso
      (kernelSubobjectIso (map π)) ≪≫
    PreservesKernel.iso (SheafOfModules.toSheaf (ringSheaf J A)) (map π)

/-- The canonical factorization of an additive-sheaf morphism whose composite with the kernel
ideal map vanishes. -/
@[stacks 01UP "additive lift to a kernel ideal",
  stacks 04BP "additive lift to a kernel ideal"]
noncomputable def additiveLift (π : A ⟶ O₂)
    {G : Sheaf J AddCommGrpCat.{w}}
    (g : G ⟶
      (SheafOfModules.toSheaf (ringSheaf J A)).obj (unitModule J A))
    (hg : g ≫ (SheafOfModules.toSheaf (ringSheaf J A)).map (map π) = 0) :
    G ⟶ (SheafOfModules.toSheaf (ringSheaf J A)).obj (sheaf π) :=
  kernel.lift _ g hg ≫ (underlyingKernelIso π).inv

/-- The additive lift followed by the underlying kernel-ideal inclusion is the original map. -/
@[reassoc, stacks 01UP "additive kernel lift specification",
  stacks 04BP "additive kernel lift specification"]
theorem additiveLift_comp_ι (π : A ⟶ O₂)
    {G : Sheaf J AddCommGrpCat.{w}}
    (g : G ⟶
      (SheafOfModules.toSheaf (ringSheaf J A)).obj (unitModule J A))
    (hg : g ≫ (SheafOfModules.toSheaf (ringSheaf J A)).map (map π) = 0) :
    additiveLift π g hg ≫
        (SheafOfModules.toSheaf (ringSheaf J A)).map (ι π) = g := sorry

end Underlying

/-- The inclusion of the kernel ideal followed by `map π` is zero. -/
theorem ι_comp_map (π : A ⟶ O₂) : ι π ≫ map π = 0 := sorry

/-- The ordinary ideal of sections annihilated by `π` on an object of the site. -/
abbrev sectionIdeal (π : A ⟶ O₂) (U : Cᵒᵖ) : Ideal (A.obj.obj U) :=
  RingHom.ker (π.hom.app U).hom

/-- Sections of the categorical kernel ideal identify canonically with the ordinary kernel ideal
of the component ring homomorphism. -/
@[stacks 01UP "kernel-ideal sections equivalence",
  stacks 04BP "kernel-ideal sections equivalence"]
noncomputable def sectionsIso (π : A ⟶ O₂) (U : Cᵒᵖ) :
    (sheaf π).val.obj U ≅ ModuleCat.of (A.obj.obj U) (sectionIdeal π U) :=
  (SheafOfModules.evaluation (ringSheaf J A) U).mapIso
      (kernelSubobjectIso (map π)) ≪≫
    PreservesKernel.iso
      (SheafOfModules.evaluation (ringSheaf J A) U) (map π) ≪≫
    ModuleCat.kernelIsoKer
      ((SheafOfModules.evaluation (ringSheaf J A) U).map (map π))

/-- The value of the kernel-ideal inclusion on a section over `U`. -/
abbrev ιApp (π : A ⟶ O₂) (U : Cᵒᵖ) (x : (sheaf π).val.obj U) : A.obj.obj U :=
  (ι π).val.app U x

/-- The forward kernel-sections equivalence has underlying map the kernel-ideal inclusion. -/
@[simp]
theorem sectionsIso_hom_coe (π : A ⟶ O₂) (U : Cᵒᵖ)
    (x : (sheaf π).val.obj U) :
    ((sectionsIso π U).hom x : A.obj.obj U) = ιApp π U x := sorry

/-- A local section of `A` belongs to the ordinary kernel ideal exactly when it comes from the
categorical kernel ideal. -/
theorem mem_sectionIdeal_iff (π : A ⟶ O₂) (U : Cᵒᵖ) (x : A.obj.obj U) :
    x ∈ sectionIdeal π U ↔ ∃ y : (sheaf π).val.obj U, ιApp π U y = x := sorry

/-- The section ideal of the categorical kernel subobject is the ordinary ring-homomorphism
kernel on every object of the site. -/
@[simp, stacks 04BP "sectionwise kernel ideal"]
theorem sections_eq_sectionIdeal (π : A ⟶ O₂) (U : Cᵒᵖ) :
    IdealSheaf.sections (subobject π) U = sectionIdeal π U := sorry

/-- Every section of the categorical kernel maps into the ordinary sectionwise kernel ideal. -/
theorem ιApp_mem_sectionIdeal (π : A ⟶ O₂) (U : Cᵒᵖ)
    (x : (sheaf π).val.obj U) : ιApp π U x ∈ sectionIdeal π U := sorry

/-- The sectionwise kernel-ideal inclusion is injective. -/
theorem ιApp_injective (π : A ⟶ O₂) (U : Cᵒᵖ) :
    Function.Injective (ιApp π U) := sorry

/-- A section in `RingHom.ker (π.app U)` has a unique preimage in the categorical kernel ideal. -/
theorem existsUnique_ιApp (π : A ⟶ O₂) (U : Cᵒᵖ) (x : A.obj.obj U)
    (hx : x ∈ sectionIdeal π U) :
    ∃! y : (sheaf π).val.obj U, ιApp π U y = x := sorry

end KernelIdeal

end SheafOfModules.RingedSite
