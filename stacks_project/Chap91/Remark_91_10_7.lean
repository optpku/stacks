module

public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import stacks_project.Chap91.Remark_91_10_7_Extension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of 08MB extensions along morphisms of first-order thickenings

After identifying underlying topoi, a morphism h of first-order thickenings of a ringed topos
(Sh(C), 𝒪) induces an 𝒪-module map ℐ₂ ⟶ ℐ₁.  Given 𝒪-modules ℱ, 𝒦ᵢ, maps
cᵢ : ℐᵢ ⊗ ℱ ⟶ 𝒦ᵢ, and k : 𝒦₂ ⟶ 𝒦₁ making the c-square commute, there is a canonical
pushout sending an 08MB extension ℱ'₂ of ℱ by 𝒦₂ as an 𝒪'₂-module with c_{ℱ'₂} = c₂
to the pushout extension ℱ'₁ of ℱ by 𝒦₁ as an 𝒪'₁-module with c_{ℱ'₁} = c₁.
The sheaf ℱ'₁ is the pushout of 𝒦₂ ⟶ ℱ'₂ along k in abelian sheaves on C; the 𝒪'₁-action
on a class from s' uses a local lift of π₁(a) through π₂, the 𝒪'₂-action, and the ℐ₁-correction
c₁((a - h(lift)) ⊗ proj(s')).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Presheaf CategoryTheory.Presieve Opposite
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace ModuleExtension

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 𝒪1 𝒪2 : Sheaf J CommRingCat.{max u v}}
variable {π1 : 𝒪1 ⟶ 𝒪} {π2 : 𝒪2 ⟶ 𝒪}
variable [Sheaf.IsLocallySurjective π1] [Sheaf.IsLocallySurjective π2]
variable {hπ1 : KernelIdeal.IsSquareZero π1} {hπ2 : KernelIdeal.IsSquareZero π2}
variable {F K1 K2 : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
variable {c1 : moduleTensor (idealModule hπ1) F ⟶ K1}
variable {c2 : moduleTensor (idealModule hπ2) F ⟶ K2}
variable (h : 𝒪2 ⟶ 𝒪1)

/-- Underlying abelian sheaf of an 𝒪-module. -/
noncomputable abbrev abelianSheaf
    (M : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    Sheaf J AddCommGrpCat.{max u v} :=
  (SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj M

/-- Underlying abelian sheaf of an 𝒪'ᵢ-module. -/
noncomputable abbrev abelianSheafOver {𝒪' : Sheaf J CommRingCat.{max u v}}
    (M : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') :
    Sheaf J AddCommGrpCat.{max u v} :=
  (SheafOfModules.toSheaf (ringSheaf J 𝒪')).obj M

/-- The underlying abelian map of ℱ'₂.incl : 𝒦₂ ⟶ ℱ'₂. Restriction of scalars does not
change underlying abelian sheaves, so this is a map 𝒦₂ ⟶ ℱ'₂ in sheaves on C. -/
noncomputable def inclUnderlying (F'2 : ModuleExtension hπ2 F K2 c2) :
    abelianSheaf K2 ⟶ abelianSheafOver F'2.module :=
  (SheafOfModules.toSheaf (ringSheaf J 𝒪2)).map F'2.incl

/-- The underlying abelian map of k : 𝒦₂ ⟶ 𝒦₁. -/
noncomputable def kernelUnderlying (k : K2 ⟶ K1) :
    abelianSheaf K2 ⟶ abelianSheaf K1 :=
  (SheafOfModules.toSheaf (ringSheaf J 𝒪)).map k

/-- After identifying underlying topoi, the sheaf ℱ'₁ is the pushout of 𝒦₂ ⟶ ℱ'₂ along
k : 𝒦₂ ⟶ 𝒦₁ in abelian sheaves on C. -/
noncomputable def pushoutUnderlying (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (F'2 : ModuleExtension hπ2 F K2 c2) :
    Sheaf J AddCommGrpCat.{max u v} :=
  Limits.pushout (inclUnderlying F'2) (kernelUnderlying k)

/-- The comparison ℱ'₂ ⟶ ℱ'₁ of middle terms is the underlying pushout inclusion. -/
noncomputable def pushoutInlSheaf (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (F'2 : ModuleExtension hπ2 F K2 c2) :
    abelianSheafOver F'2.module ⟶ pushoutUnderlying h h_comm k F'2 :=
  Limits.pushout.inl (inclUnderlying F'2) (kernelUnderlying k)

/-- The 𝒦₁-leg of the abelian pushout. -/
noncomputable def pushoutInrSheaf (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (F'2 : ModuleExtension hπ2 F K2 c2) :
    abelianSheaf K1 ⟶ pushoutUnderlying h h_comm k F'2 :=
  Limits.pushout.inr (inclUnderlying F'2) (kernelUnderlying k)

/-- The two legs of the extension square agree after projection to ℱ as abelian sheaves. -/
theorem pushout_proj_desc_comm (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (F'2 : ModuleExtension hπ2 F K2 c2) :
    inclUnderlying F'2 ≫ (SheafOfModules.toSheaf (ringSheaf J 𝒪2)).map F'2.proj =
      kernelUnderlying k ≫ (0 : abelianSheaf K1 ⟶ abelianSheaf F) := sorry

/-- The projection ℱ'₁ ⟶ ℱ of the extension diagram, as a map of abelian sheaves. -/
noncomputable def projUnderlying (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (F'2 : ModuleExtension hπ2 F K2 c2) :
    pushoutUnderlying h h_comm k F'2 ⟶ abelianSheaf F :=
  Limits.pushout.desc
    ((SheafOfModules.toSheaf (ringSheaf J 𝒪2)).map F'2.proj)
    (0 : abelianSheaf K1 ⟶ abelianSheaf F)
    (pushout_proj_desc_comm h h_comm k F'2)

/-- Pointwise biproduct of ℱ'₂ and 𝒦₁, whose classes generate the abelian pushout. -/
noncomputable def generatorBiprod (k : K2 ⟶ K1) (F'2 : ModuleExtension hπ2 F K2 c2) :
    Cᵒᵖ ⥤ AddCommGrpCat.{max u v} where
  obj U := (abelianSheafOver F'2.module).obj.obj U ⊞ (abelianSheaf K1).obj.obj U
  map f := biprod.map
    ((abelianSheafOver F'2.module).obj.map f) ((abelianSheaf K1).obj.map f)
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The canonical map from generating pairs (s', x) to the abelian pushout. -/
noncomputable def generatorBiprodToPushout (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (F'2 : ModuleExtension hπ2 F K2 c2) :
    generatorBiprod k F'2 ⟶ (pushoutUnderlying h h_comm k F'2).obj where
  app U := biprod.desc
    ((InducedCategory.Hom.hom (pushoutInlSheaf h h_comm k F'2)).app U)
    ((InducedCategory.Hom.hom (pushoutInrSheaf h h_comm k F'2)).app U)
  naturality := sorry

/-- Classes of the abelian pushout are locally represented by pairs from ℱ'₂ and 𝒦₁. -/
instance instIsLocallySurjective_generatorBiprodToPushout
    (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1) (F'2 : ModuleExtension hπ2 F K2 c2) :
    IsLocallySurjective J (generatorBiprodToPushout h h_comm k F'2) := sorry

/-- The kernel-ideal section of a - h(b) when π₁(a) = π₂(b). -/
noncomputable def idealSectionOfDifference (U : Cᵒᵖ)
    (a : 𝒪1.obj.obj U) (b : 𝒪2.obj.obj U) :
    (KernelIdeal.sheaf π1).val.obj U :=
  (KernelIdeal.sectionsIso π1 U).inv
    ⟨a - (h.hom.app U).hom b, sorry⟩

/-- The ℐ₁-correction c₁((a - h(b)) ⊗ proj(s')) in 𝒦₁. -/
noncomputable def c1Correction (hπ1 : KernelIdeal.IsSquareZero π1)
    (c1 : moduleTensor (idealModule hπ1) F ⟶ K1)
    (F'2 : ModuleExtension hπ2 F K2 c2) (U : Cᵒᵖ)
    (a : 𝒪1.obj.obj U) (b : 𝒪2.obj.obj U) (s' : F'2.module.val.obj U) :
    K1.val.obj U :=
  (c1.val.app U).hom
    (tensorSection 𝒪 U
      (((restrictIdealModuleIso hπ1).inv.val.app U).hom
        (idealSectionOfDifference h U a b))
      ((F'2.proj.val.app U).hom s'))

/-- Local 𝒪'₁-action on a class coming from s' in ℱ'₂: act by a lift of π₁(a) through π₂,
then correct by c₁((a - h(lift)) ⊗ proj(s')). -/
noncomputable def actionOnClassFrom (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (c1 : moduleTensor (idealModule hπ1) F ⟶ K1)
    (F'2 : ModuleExtension hπ2 F K2 c2) (U : Cᵒᵖ)
    (a : 𝒪1.obj.obj U) (b : 𝒪2.obj.obj U) (s' : F'2.module.val.obj U) :
    (pushoutUnderlying h h_comm k F'2).obj.obj U :=
  let bR : (forget₂ CommRingCat.{max u v} RingCat.{max u v}).obj (𝒪2.obj.obj U) := b
  let sAct := CategoryTheory.ConcreteCategory.hom ((F'2.module.val.obj U).smul bR) s'
  let corr : K1.val.obj U := c1Correction h hπ1 c1 F'2 U a b s'
  ((InducedCategory.Hom.hom (pushoutInlSheaf h h_comm k F'2)).app U) sAct +
    ((InducedCategory.Hom.hom (pushoutInrSheaf h h_comm k F'2)).app U) corr

/-- 𝒪'₁ acts on 𝒦₁ through π₁. -/
noncomputable def actionOnKernel (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (F'2 : ModuleExtension hπ2 F K2 c2) (U : Cᵒᵖ)
    (a : 𝒪1.obj.obj U) (x : K1.val.obj U) :
    (pushoutUnderlying h h_comm k F'2).obj.obj U :=
  let aO : (forget₂ CommRingCat.{max u v} RingCat.{max u v}).obj (𝒪.obj.obj U) :=
    (π1.hom.app U).hom a
  let xAct := CategoryTheory.ConcreteCategory.hom ((K1.val.obj U).smul aO) x
  ((InducedCategory.Hom.hom (pushoutInrSheaf h h_comm k F'2)).app U) xAct

/-- The covering sieve on which π₁(a) lifts through π₂ and the pushout class is represented
by a pair from ℱ'₂ and 𝒦₁. -/
noncomputable def pushoutActionSieve (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (F'2 : ModuleExtension hπ2 F K2 c2) (U : Cᵒᵖ)
    (a : 𝒪1.obj.obj U) (s : (pushoutUnderlying h h_comm k F'2).obj.obj U) :
    Sieve U.unop :=
  imageSieve π2.hom ((π1.hom.app U).hom a) ⊓
    imageSieve (generatorBiprodToPushout h h_comm k F'2) s

/-- The action sieve covers the object of the site. -/
theorem pushoutActionSieve_mem (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (F'2 : ModuleExtension hπ2 F K2 c2) (U : Cᵒᵖ)
    (a : 𝒪1.obj.obj U) (s : (pushoutUnderlying h h_comm k F'2).obj.obj U) :
    pushoutActionSieve h h_comm k F'2 U a s ∈ J U.unop := sorry

/-- Type-valued underlying presheaf of the abelian pushout. -/
noncomputable abbrev pushoutUnderlyingType (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (F'2 : ModuleExtension hπ2 F K2 c2) : Cᵒᵖ ⥤ Type (max u v) :=
  (pushoutUnderlying h h_comm k F'2).obj ⋙ CategoryTheory.forget AddCommGrpCat.{max u v}

/-- The underlying abelian pushout is a type-valued sheaf, so compatible local action
families amalgamate. -/
theorem pushoutUnderlying_isTypeSheaf (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (F'2 : ModuleExtension hπ2 F K2 c2) :
    Presieve.IsSheaf J (pushoutUnderlyingType h h_comm k F'2) := sorry

/-- Local action of a on a generating pair, using a lift of π₁(a) through π₂. -/
noncomputable def actionOnGeneratingPair (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (hc : CommSq c2 (moduleTensorMap (idealMap h h_comm hπ1 hπ2) (𝟙 F)) k c1)
    (F'2 : ModuleExtension hπ2 F K2 c2) {U : Cᵒᵖ}
    {V : C} (g : V ⟶ U.unop)
    (a : 𝒪1.obj.obj U) (s : (pushoutUnderlying h h_comm k F'2).obj.obj U)
    (hg : pushoutActionSieve h h_comm k F'2 U a s g) :
    (pushoutUnderlying h h_comm k F'2).obj.obj (op V) :=
  let b := localPreimage π2.hom ((π1.hom.app U).hom a) g hg.1
  let pair : (generatorBiprod k F'2).obj (op V) :=
    localPreimage (generatorBiprodToPushout h h_comm k F'2) s g hg.2
  let fst : (generatorBiprod k F'2).obj (op V) ⟶
      (abelianSheafOver F'2.module).obj.obj (op V) := biprod.fst
  let snd : (generatorBiprod k F'2).obj (op V) ⟶
      (abelianSheaf K1).obj.obj (op V) := biprod.snd
  let s' := CategoryTheory.ConcreteCategory.hom fst pair
  let x := CategoryTheory.ConcreteCategory.hom snd pair
  actionOnClassFrom h h_comm k c1 F'2 (op V) (𝒪1.obj.map g.op a) b s' +
    actionOnKernel h h_comm k F'2 (op V) (𝒪1.obj.map g.op a) x

/-- The local action family on the covering sieve, as a type-valued family of elements. -/
noncomputable def actionFamily (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (hc : CommSq c2 (moduleTensorMap (idealMap h h_comm hπ1 hπ2) (𝟙 F)) k c1)
    (F'2 : ModuleExtension hπ2 F K2 c2) (U : Cᵒᵖ)
    (a : 𝒪1.obj.obj U) (s : (pushoutUnderlying h h_comm k F'2).obj.obj U) :
    FamilyOfElements (pushoutUnderlyingType h h_comm k F'2)
      (pushoutActionSieve h h_comm k F'2 U a s).arrows :=
  fun _ g hg ↦ actionOnGeneratingPair h h_comm k hc F'2 g a s hg

/-- Compatibility of the local action family; uses commutativity of the c-square and
idealMap to compare two lifts. -/
theorem actionOnGeneratingPair_compatible (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (hc : CommSq c2 (moduleTensorMap (idealMap h h_comm hπ1 hπ2) (𝟙 F)) k c1)
    (F'2 : ModuleExtension hπ2 F K2 c2) (U : Cᵒᵖ)
    (a : 𝒪1.obj.obj U) (s : (pushoutUnderlying h h_comm k F'2).obj.obj U) :
    FamilyOfElements.Compatible (actionFamily h h_comm k hc F'2 U a s) := sorry

/-- Objectwise 𝒪'₁-action on the abelian pushout, amalgamating the local-lift formula. -/
noncomputable def pushoutSMul (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (hc : CommSq c2 (moduleTensorMap (idealMap h h_comm hπ1 hπ2) (𝟙 F)) k c1)
    (F'2 : ModuleExtension hπ2 F K2 c2) (U : Cᵒᵖ)
    (a : (ringSheaf J 𝒪1).obj.obj U)
    (s : (pushoutUnderlying h h_comm k F'2).obj.obj U) :
    (pushoutUnderlying h h_comm k F'2).obj.obj U :=
  (pushoutUnderlying_isTypeSheaf h h_comm k F'2
      (pushoutActionSieve h h_comm k F'2 U a s)
      (pushoutActionSieve_mem h h_comm k F'2 U a s)).amalgamate
    (actionFamily h h_comm k hc F'2 U a s)
    (actionOnGeneratingPair_compatible h h_comm k hc F'2 U a s)

/-- The local 𝒪'₁-module structure on sections of the abelian pushout. -/
@[reducible] noncomputable def pushoutSectionModule (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (hc : CommSq c2 (moduleTensorMap (idealMap h h_comm hπ1 hπ2) (𝟙 F)) k c1)
    (F'2 : ModuleExtension hπ2 F K2 c2) (U : Cᵒᵖ) :
    Module ((ringSheaf J 𝒪1).obj.obj U)
      ((pushoutUnderlying h h_comm k F'2).obj.obj U) where
  smul := pushoutSMul h h_comm k hc F'2 U
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The abelian pushout, equipped with the 𝒪'₁-module structure whose action on a class
from s' uses a local lift of π₁(a) through π₂, the 𝒪'₂-action, and the ℐ₁-correction. -/
noncomputable def pushoutModule (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (hc : CommSq c2 (moduleTensorMap (idealMap h h_comm hπ1 hπ2) (𝟙 F)) k c1)
    (F'2 : ModuleExtension hπ2 F K2 c2) :
    ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪1 where
  val :=
    @PresheafOfModules.ofPresheaf C _ (ringSheaf J 𝒪1).obj
      (pushoutUnderlying h h_comm k F'2).obj
      (fun X ↦ pushoutSectionModule h h_comm k hc F'2 X)
      (fun {X Y} f r m ↦ sorry)
  isSheaf := (pushoutUnderlying h h_comm k F'2).property

/-- The inclusion 𝒦₁ ⟶ ℱ'₁ is the 𝒦₁-leg of the abelian pushout. -/
noncomputable def pushoutIncl (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (hc : CommSq c2 (moduleTensorMap (idealMap h h_comm hπ1 hπ2) (𝟙 F)) k c1)
    (F'2 : ModuleExtension hπ2 F K2 c2) :
    (restrictionAlong π1).obj K1 ⟶ pushoutModule h h_comm k hc F'2 where
  val := PresheafOfModules.homMk (pushoutInrSheaf h h_comm k F'2).hom sorry

/-- The projection ℱ'₁ ⟶ ℱ is the pushout description of ℱ'₂.proj and the zero map on 𝒦₁. -/
noncomputable def pushoutProj (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (hc : CommSq c2 (moduleTensorMap (idealMap h h_comm hπ1 hπ2) (𝟙 F)) k c1)
    (F'2 : ModuleExtension hπ2 F K2 c2) :
    pushoutModule h h_comm k hc F'2 ⟶ (restrictionAlong π1).obj F where
  val := PresheafOfModules.homMk (projUnderlying h h_comm k F'2).hom sorry

/-- Remark 91.10.7: after identifying underlying topoi, a morphism h of first-order
thickenings of a ringed topos (Sh(C), 𝒪) induces an 𝒪-module map ℐ₂ ⟶ ℐ₁ of square-zero
ideal sheaves. Given 𝒪-modules ℱ, 𝒦ᵢ, maps cᵢ : ℐᵢ ⊗ ℱ ⟶ 𝒦ᵢ, and k : 𝒦₂ ⟶ 𝒦₁ making
the c-square commute, this is the canonical pushout sending an 08MB extension ℱ'₂ of ℱ
by 𝒦₂ as an 𝒪'₂-module with c_{ℱ'₂} = c₂ to the pushout extension ℱ'₁ of ℱ by 𝒦₁ as an
𝒪'₁-module with c_{ℱ'₁} = c₁. The sheaf ℱ'₁ is the pushout of 𝒦₂ ⟶ ℱ'₂ along k in
abelian sheaves on C; the 𝒪'₁-action on a class from s' uses a local lift of π₁(a)
through π₂, the 𝒪'₂-action, and the ℐ₁-correction c₁((a - h(lift)) ⊗ proj(s')). -/
@[stacks 08MJ]
noncomputable def pushout (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (hc : CommSq c2 (moduleTensorMap (idealMap h h_comm hπ1 hπ2) (𝟙 F)) k c1)
    (F'2 : ModuleExtension hπ2 F K2 c2) :
    ModuleExtension hπ1 F K1 c1 :=
  of (pushoutModule h h_comm k hc F'2)
    (pushoutIncl h h_comm k hc F'2) (pushoutProj h h_comm k hc F'2)

/-- The underlying 𝒪'₁-module of the 08MB pushout. -/
noncomputable abbrev pushoutSheaf (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (hc : CommSq c2 (moduleTensorMap (idealMap h h_comm hπ1 hπ2) (𝟙 F)) k c1)
    (F'2 : ModuleExtension hπ2 F K2 c2) :
    ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪1 :=
  (pushout h h_comm k hc F'2).module

/-- The comparison ℱ'₂ ⟶ ℱ'₁ of middle terms induced by the abelian pushout. -/
noncomputable def pushoutInl (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (hc : CommSq c2 (moduleTensorMap (idealMap h h_comm hπ1 hπ2) (𝟙 F)) k c1)
    (F'2 : ModuleExtension hπ2 F K2 c2) :
    abelianSheafOver F'2.module ⟶ pushoutUnderlying h h_comm k F'2 :=
  pushoutInlSheaf h h_comm k F'2

/-- Forgetting the 𝒪'₁-action recovers the abelian pushout of 𝒦₂ ⟶ ℱ'₂ along k. -/
theorem pushoutSheaf_toSheaf (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (hc : CommSq c2 (moduleTensorMap (idealMap h h_comm hπ1 hπ2) (𝟙 F)) k c1)
    (F'2 : ModuleExtension hπ2 F K2 c2) :
    abelianSheafOver (pushoutSheaf h h_comm k hc F'2) =
      pushoutUnderlying h h_comm k F'2 := sorry

/-- The 08MB pushout is short exact, recovers c₁, and realises the pushout diagram of
extensions in abelian sheaves. -/
theorem pushout_spec (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (hc : CommSq c2 (moduleTensorMap (idealMap h h_comm hπ1 hπ2) (𝟙 F)) k c1)
    (F'2 : ModuleExtension hπ2 F K2 c2) :
    (toShortComplex (pushout h h_comm k hc F'2)).ShortExact ∧
      CompatibleC hπ1 (pushout h h_comm k hc F'2).incl
        (pushout h h_comm k hc F'2).proj c1 ∧
      IsPushout (inclUnderlying F'2) (kernelUnderlying k)
        (pushoutInl h h_comm k hc F'2)
        (pushoutInrSheaf h h_comm k F'2) := sorry

/-- The underlying diagram of the 08MB pushout is a pushout square in abelian sheaves on C. -/
theorem pushout_isPushout (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (hc : CommSq c2 (moduleTensorMap (idealMap h h_comm hπ1 hπ2) (𝟙 F)) k c1)
    (F'2 : ModuleExtension hπ2 F K2 c2) :
    IsPushout (inclUnderlying F'2) (kernelUnderlying k)
      (pushoutInl h h_comm k hc F'2) (pushoutInrSheaf h h_comm k F'2) := sorry

/-- The objectwise 𝒪'₁-action on a class from s' is the local-lift formula. -/
theorem pushoutSMul_spec (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (hc : CommSq c2 (moduleTensorMap (idealMap h h_comm hπ1 hπ2) (𝟙 F)) k c1)
    (F'2 : ModuleExtension hπ2 F K2 c2) (U : Cᵒᵖ)
    (a : 𝒪1.obj.obj U) (b : 𝒪2.obj.obj U)
    (hb : (π2.hom.app U).hom b = (π1.hom.app U).hom a)
    (s' : F'2.module.val.obj U) :
    pushoutSMul h h_comm k hc F'2 U a
        (CategoryTheory.ConcreteCategory.hom
          ((InducedCategory.Hom.hom (pushoutInlSheaf h h_comm k F'2)).app U) s') =
      actionOnClassFrom h h_comm k c1 F'2 U a b s' := sorry

end ModuleExtension
end SheafOfModules.RingedSite.FirstOrderThickening
