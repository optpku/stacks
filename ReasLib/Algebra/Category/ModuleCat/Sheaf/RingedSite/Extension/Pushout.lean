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
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension.Map

/-!
# Pushouts of mixed-scalar extensions

A compatible change of square-zero presentation and kernel coefficients equips the additive
pushout of an extension with the target scalar action and the prescribed infinitesimal map.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Presheaf CategoryTheory.Presieve Opposite
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening.Extension

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
variable {K1 K2 : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
variable (E₂ : Extension π2)
variable {c1 : moduleTensor (idealModule hπ1) E₂.quot ⟶ K1}
variable (h : 𝒪2 ⟶ 𝒪1)

/-- The underlying additive inclusion of a mixed-scalar extension. -/
@[expose] noncomputable def inclUnderlying :
    (SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj E₂.kernel ⟶
      (SheafOfModules.toSheaf (ringSheaf J 𝒪2)).obj E₂.middle :=
  (SheafOfModules.toSheaf (ringSheaf J 𝒪2)).map E₂.ι

/-- The underlying abelian map of k : 𝒦₂ ⟶ 𝒦₁. -/
@[expose] noncomputable def kernelUnderlying (k : K2 ⟶ K1) :
    (SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj K2 ⟶
      (SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj K1 :=
  (SheafOfModules.toSheaf (ringSheaf J 𝒪)).map k

/-- The additive pushout of an extension inclusion along a map of kernel coefficients. -/
@[expose] noncomputable def pushoutUnderlying (k : E₂.kernel ⟶ K1) :
    Sheaf J AddCommGrpCat.{max u v} :=
  Limits.pushout (inclUnderlying E₂) (kernelUnderlying k)

/-- The comparison ℱ'₂ ⟶ ℱ'₁ of middle terms is the underlying pushout inclusion. -/
@[expose] noncomputable def pushoutInlSheaf (k : E₂.kernel ⟶ K1) :
    (SheafOfModules.toSheaf (ringSheaf J 𝒪2)).obj E₂.middle ⟶ pushoutUnderlying E₂ k :=
  Limits.pushout.inl (inclUnderlying E₂) (kernelUnderlying k)

/-- The 𝒦₁-leg of the abelian pushout. -/
@[expose] noncomputable def pushoutInrSheaf (k : E₂.kernel ⟶ K1) :
    (SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj K1 ⟶ pushoutUnderlying E₂ k :=
  Limits.pushout.inr (inclUnderlying E₂) (kernelUnderlying k)

/-- The two legs of the extension square agree after projection to ℱ as abelian sheaves. -/
theorem pushout_proj_desc_comm (k : E₂.kernel ⟶ K1) :
    inclUnderlying E₂ ≫ (SheafOfModules.toSheaf (ringSheaf J 𝒪2)).map E₂.p =
      kernelUnderlying k ≫
        (0 : (SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj K1 ⟶
          (SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj E₂.quot) := sorry

/-- The projection ℱ'₁ ⟶ ℱ of the extension diagram, as a map of abelian sheaves. -/
@[expose] noncomputable def projUnderlying (k : E₂.kernel ⟶ K1) :
    pushoutUnderlying E₂ k ⟶ (SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj E₂.quot :=
  Limits.pushout.desc
    ((SheafOfModules.toSheaf (ringSheaf J 𝒪2)).map E₂.p)
    (0 : (SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj K1 ⟶
      (SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj E₂.quot)
    (pushout_proj_desc_comm E₂ k)

/-- The restriction maps of generating pairs preserve identities. -/
theorem generatorBiprod_map_id (U : Cᵒᵖ) :
    biprod.map (E₂.middle.val.presheaf.map (𝟙 U)) (K1.val.presheaf.map (𝟙 U)) =
      𝟙 (E₂.middle.val.presheaf.obj U ⊞ K1.val.presheaf.obj U) := sorry

/-- The restriction maps of generating pairs preserve composition. -/
theorem generatorBiprod_map_comp {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    biprod.map (E₂.middle.val.presheaf.map (f ≫ g)) (K1.val.presheaf.map (f ≫ g)) =
      biprod.map (E₂.middle.val.presheaf.map f) (K1.val.presheaf.map f) ≫
        biprod.map (E₂.middle.val.presheaf.map g) (K1.val.presheaf.map g) := sorry

/-- Pointwise biproduct of ℱ'₂ and 𝒦₁, whose classes generate the abelian pushout. -/
@[expose] noncomputable def generatorBiprod (k : E₂.kernel ⟶ K1) :
    Cᵒᵖ ⥤ AddCommGrpCat.{max u v} where
  obj U := E₂.middle.val.presheaf.obj U ⊞ K1.val.presheaf.obj U
  map f := biprod.map
    (E₂.middle.val.presheaf.map f) (K1.val.presheaf.map f)
  map_id U := generatorBiprod_map_id E₂ U
  map_comp f g := generatorBiprod_map_comp E₂ f g

/-- The map from generating pairs to the additive pushout commutes with restriction. -/
theorem generatorBiprodToPushout_naturality (k : E₂.kernel ⟶ K1)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (generatorBiprod E₂ k).map f ≫
        biprod.desc ((pushoutInlSheaf E₂ k).hom.app V) ((pushoutInrSheaf E₂ k).hom.app V) =
      biprod.desc ((pushoutInlSheaf E₂ k).hom.app U) ((pushoutInrSheaf E₂ k).hom.app U) ≫
        (pushoutUnderlying E₂ k).obj.map f := sorry

/-- The canonical map from generating pairs (s', x) to the abelian pushout. -/
@[expose] noncomputable def generatorBiprodToPushout (k : E₂.kernel ⟶ K1) :
    generatorBiprod E₂ k ⟶ (pushoutUnderlying E₂ k).obj where
  app U := biprod.desc
    ((InducedCategory.Hom.hom (pushoutInlSheaf E₂ k)).app U)
    ((InducedCategory.Hom.hom (pushoutInrSheaf E₂ k)).app U)
  naturality _ _ f := generatorBiprodToPushout_naturality E₂ k f

/-- Every section of the additive pushout is locally represented by a generating pair. -/
theorem generatorBiprod_imageSieve_mem (k : E₂.kernel ⟶ K1) (U : Cᵒᵖ)
    (s : (pushoutUnderlying E₂ k).obj.obj U) :
    imageSieve (generatorBiprodToPushout E₂ k) s ∈ J U.unop := sorry

/-- The kernel-ideal section of a - h(b) for a compatible lift with π₁(a) = π₂(b). -/
private noncomputable def idealSectionOfDifference (h_comm : h ≫ π1 = π2) (U : Cᵒᵖ)
    (a : 𝒪1.obj.obj U) (b : 𝒪2.obj.obj U)
    (hb : (π2.hom.app U).hom b = (π1.hom.app U).hom a) :
    (KernelIdeal.sheaf π1).val.obj U :=
  (KernelIdeal.sectionsIso π1 U).inv
    ⟨a - (h.hom.app U).hom b, by
      change (π1.hom.app U).hom (a - (h.hom.app U).hom b) = 0
      have hU : (π1.hom.app U).hom ((h.hom.app U).hom b) = (π2.hom.app U).hom b :=
        congrArg (fun f : 𝒪2 ⟶ 𝒪 ↦ (f.hom.app U).hom b) h_comm
      rw [map_sub, hU, hb, sub_self]⟩

/-- The ℐ₁-correction c₁((a - h(b)) ⊗ proj(s')) in 𝒦₁. -/
private noncomputable def c1Correction (h_comm : h ≫ π1 = π2) (hπ1 : KernelIdeal.IsSquareZero π1)
    (c1 : moduleTensor (idealModule hπ1) E₂.quot ⟶ K1)
    (U : Cᵒᵖ)
    (a : 𝒪1.obj.obj U) (b : 𝒪2.obj.obj U)
    (hb : (π2.hom.app U).hom b = (π1.hom.app U).hom a)
    (s' : E₂.middle.val.obj U) :
    K1.val.obj U :=
  (c1.val.app U).hom
    (tensorSection 𝒪 U
      (((restrictIdealModuleIso hπ1).inv.val.app U).hom
        (idealSectionOfDifference h h_comm U a b hb))
      ((E₂.p.val.app U).hom s'))

/-- Local 𝒪'₁-action on a class coming from s' in ℱ'₂: act by a lift of π₁(a) through π₂,
then correct by c₁((a - h(lift)) ⊗ proj(s')). -/
noncomputable def actionOnClassFrom (h_comm : h ≫ π1 = π2) (k : E₂.kernel ⟶ K1)
    (c1 : moduleTensor (idealModule hπ1) E₂.quot ⟶ K1)
    (U : Cᵒᵖ)
    (a : 𝒪1.obj.obj U) (b : 𝒪2.obj.obj U)
    (hb : (π2.hom.app U).hom b = (π1.hom.app U).hom a)
    (s' : E₂.middle.val.obj U) :
    (pushoutUnderlying E₂ k).obj.obj U :=
  let bR : (forget₂ CommRingCat.{max u v} RingCat.{max u v}).obj (𝒪2.obj.obj U) := b
  let sAct := CategoryTheory.ConcreteCategory.hom ((E₂.middle.val.obj U).smul bR) s'
  let corr : K1.val.obj U := c1Correction E₂ h h_comm hπ1 c1 U a b hb s'
  ((InducedCategory.Hom.hom (pushoutInlSheaf E₂ k)).app U) sAct +
    ((InducedCategory.Hom.hom (pushoutInrSheaf E₂ k)).app U) corr

/-- 𝒪'₁ acts on 𝒦₁ through π₁. -/
noncomputable def actionOnKernel (h_comm : h ≫ π1 = π2) (k : E₂.kernel ⟶ K1)
    (U : Cᵒᵖ)
    (a : 𝒪1.obj.obj U) (x : K1.val.obj U) :
    (pushoutUnderlying E₂ k).obj.obj U :=
  let aO : (forget₂ CommRingCat.{max u v} RingCat.{max u v}).obj (𝒪.obj.obj U) :=
    (π1.hom.app U).hom a
  let xAct := CategoryTheory.ConcreteCategory.hom ((K1.val.obj U).smul aO) x
  ((InducedCategory.Hom.hom (pushoutInrSheaf E₂ k)).app U) xAct

/-- The covering sieve on which π₁(a) lifts through π₂ and the pushout class is represented
by a pair from ℱ'₂ and 𝒦₁. -/
@[expose] noncomputable def pushoutActionSieve (h_comm : h ≫ π1 = π2) (k : E₂.kernel ⟶ K1)
    (U : Cᵒᵖ)
    (a : 𝒪1.obj.obj U) (s : (pushoutUnderlying E₂ k).obj.obj U) :
    Sieve U.unop :=
  imageSieve π2.hom ((π1.hom.app U).hom a) ⊓
    imageSieve (generatorBiprodToPushout E₂ k) s

/-- The action sieve covers the object of the site. -/
theorem pushoutActionSieve_mem (h_comm : h ≫ π1 = π2) (k : E₂.kernel ⟶ K1)
    (U : Cᵒᵖ)
    (a : 𝒪1.obj.obj U) (s : (pushoutUnderlying E₂ k).obj.obj U) :
    pushoutActionSieve E₂ h h_comm k U a s ∈ J U.unop := by
  apply J.intersection_covering ?_ (generatorBiprod_imageSieve_mem E₂ k U s)
  sorry

/-- A local preimage on the action sieve has the required equality of the two base sections. -/
theorem localPreimage_lift_eq (h_comm : h ≫ π1 = π2) (k : E₂.kernel ⟶ K1)
    {U : Cᵒᵖ} {V : C}
    (g : V ⟶ U.unop) (a : 𝒪1.obj.obj U)
    (s : (pushoutUnderlying E₂ k).obj.obj U)
    (hg : pushoutActionSieve E₂ h h_comm k U a s g) :
    (π2.hom.app (op V)).hom
        (localPreimage π2.hom ((π1.hom.app U).hom a) g hg.1) =
      (π1.hom.app (op V)).hom ((𝒪1.obj).map g.op a) := sorry

/-- Type-valued underlying presheaf of the abelian pushout. -/
noncomputable abbrev pushoutUnderlyingType (k : E₂.kernel ⟶ K1) : Cᵒᵖ ⥤ Type (max u v) :=
  (pushoutUnderlying E₂ k).obj ⋙ CategoryTheory.forget AddCommGrpCat.{max u v}

/-- The underlying abelian pushout is a type-valued sheaf, so compatible local action
families amalgamate. -/
theorem pushoutUnderlying_isTypeSheaf (k : E₂.kernel ⟶ K1) :
    Presieve.IsSheaf J (pushoutUnderlyingType E₂ k) := sorry

/-- Local action of a on a generating pair, using a lift of π₁(a) through π₂. -/
private noncomputable def actionOnGeneratingPair (h_comm : h ≫ π1 = π2) (k : E₂.kernel ⟶ K1)
    (hc : CommSq (infMap hπ2 E₂)
      (moduleTensorMap (KernelIdeal.IsSquareZero.mapToTarget h h_comm hπ1 hπ2) (𝟙 E₂.quot)) k c1)
    {U : Cᵒᵖ}
    {V : C} (g : V ⟶ U.unop)
    (a : 𝒪1.obj.obj U) (s : (pushoutUnderlying E₂ k).obj.obj U)
    (hg : pushoutActionSieve E₂ h h_comm k U a s g) :
    (pushoutUnderlying E₂ k).obj.obj (op V) :=
  let b := localPreimage π2.hom ((π1.hom.app U).hom a) g hg.1
  let pair : (generatorBiprod E₂ k).obj (op V) :=
    localPreimage (generatorBiprodToPushout E₂ k) s g hg.2
  let fst : (generatorBiprod E₂ k).obj (op V) ⟶
      E₂.middle.val.presheaf.obj (op V) := biprod.fst
  let snd : (generatorBiprod E₂ k).obj (op V) ⟶
      K1.val.presheaf.obj (op V) := biprod.snd
  let s' := CategoryTheory.ConcreteCategory.hom fst pair
  let x := CategoryTheory.ConcreteCategory.hom snd pair
  let hb := localPreimage_lift_eq E₂ h h_comm k g a s hg
  actionOnClassFrom E₂ h h_comm k c1 (op V) (𝒪1.obj.map g.op a) b hb s' +
    actionOnKernel E₂ h h_comm k (op V) (𝒪1.obj.map g.op a) x

/-- The local action family on the covering sieve, as a type-valued family of elements. -/
private noncomputable def actionFamily (h_comm : h ≫ π1 = π2) (k : E₂.kernel ⟶ K1)
    (hc : CommSq (infMap hπ2 E₂)
      (moduleTensorMap (KernelIdeal.IsSquareZero.mapToTarget h h_comm hπ1 hπ2) (𝟙 E₂.quot)) k c1)
    (U : Cᵒᵖ)
    (a : 𝒪1.obj.obj U) (s : (pushoutUnderlying E₂ k).obj.obj U) :
    FamilyOfElements (pushoutUnderlyingType E₂ k)
      (pushoutActionSieve E₂ h h_comm k U a s).arrows :=
  fun _ g hg ↦ actionOnGeneratingPair E₂ h h_comm k hc g a s hg

/-- Compatibility of the local action family; uses commutativity of the c-square and
the induced ideal map to compare two lifts. -/
private theorem actionOnGeneratingPair_compatible (h_comm : h ≫ π1 = π2) (k : E₂.kernel ⟶ K1)
    (hc : CommSq (infMap hπ2 E₂)
      (moduleTensorMap (KernelIdeal.IsSquareZero.mapToTarget h h_comm hπ1 hπ2) (𝟙 E₂.quot)) k c1)
    (U : Cᵒᵖ)
    (a : 𝒪1.obj.obj U) (s : (pushoutUnderlying E₂ k).obj.obj U) :
    FamilyOfElements.Compatible (actionFamily E₂ h h_comm k hc U a s) := sorry

/-- Objectwise 𝒪'₁-action on the abelian pushout, amalgamating the local-lift formula. -/
noncomputable def pushoutSMul (h_comm : h ≫ π1 = π2) (k : E₂.kernel ⟶ K1)
    (hc : CommSq (infMap hπ2 E₂)
      (moduleTensorMap (KernelIdeal.IsSquareZero.mapToTarget h h_comm hπ1 hπ2) (𝟙 E₂.quot)) k c1)
    (U : Cᵒᵖ)
    (a : (ringSheaf J 𝒪1).obj.obj U)
    (s : (pushoutUnderlying E₂ k).obj.obj U) :
    (pushoutUnderlying E₂ k).obj.obj U :=
  (pushoutUnderlying_isTypeSheaf E₂ k
      (pushoutActionSieve E₂ h h_comm k U a s)
      (pushoutActionSieve_mem E₂ h h_comm k U a s)).amalgamate
    (actionFamily E₂ h h_comm k hc U a s)
    (actionOnGeneratingPair_compatible E₂ h h_comm k hc U a s)

variable (h_comm : h ≫ π1 = π2) (k : E₂.kernel ⟶ K1)
variable (hc : CommSq (infMap hπ2 E₂)
  (moduleTensorMap (KernelIdeal.IsSquareZero.mapToTarget h h_comm hπ1 hπ2) (𝟙 E₂.quot)) k c1)

/-- Scalar multiplication on a class from the original middle term is given by any compatible
local lift and the prescribed infinitesimal correction. -/
theorem pushoutSMul_spec (U : Cᵒᵖ) (a : 𝒪1.obj.obj U) (b : 𝒪2.obj.obj U)
    (hb : (π2.hom.app U).hom b = (π1.hom.app U).hom a)
    (s' : E₂.middle.val.obj U) :
    pushoutSMul E₂ h h_comm k hc U a ((pushoutInlSheaf E₂ k).hom.app U s') =
      actionOnClassFrom E₂ h h_comm k c1 U a b hb s' := sorry

/-- The unit scalar acts identically on the additive pushout. -/
theorem pushoutSMul_one_smul (U : Cᵒᵖ) (s : (pushoutUnderlying E₂ k).obj.obj U) :
    pushoutSMul E₂ h h_comm k hc U 1 s = s := sorry

/-- Multiplication of scalars agrees with successive scalar actions on the additive pushout. -/
theorem pushoutSMul_mul_smul (U : Cᵒᵖ) (a b : (ringSheaf J 𝒪1).obj.obj U)
    (s : (pushoutUnderlying E₂ k).obj.obj U) :
    pushoutSMul E₂ h h_comm k hc U (a * b) s =
      pushoutSMul E₂ h h_comm k hc U a (pushoutSMul E₂ h h_comm k hc U b s) := sorry

/-- Every scalar annihilates the zero section of the additive pushout. -/
theorem pushoutSMul_smul_zero (U : Cᵒᵖ) (a : (ringSheaf J 𝒪1).obj.obj U) :
    pushoutSMul E₂ h h_comm k hc U a 0 = 0 := sorry

/-- Scalar multiplication distributes over addition of pushout sections. -/
theorem pushoutSMul_smul_add (U : Cᵒᵖ) (a : (ringSheaf J 𝒪1).obj.obj U)
    (s t : (pushoutUnderlying E₂ k).obj.obj U) :
    pushoutSMul E₂ h h_comm k hc U a (s + t) =
      pushoutSMul E₂ h h_comm k hc U a s + pushoutSMul E₂ h h_comm k hc U a t := sorry

/-- Addition of scalars distributes over their action on the additive pushout. -/
theorem pushoutSMul_add_smul (U : Cᵒᵖ) (a b : (ringSheaf J 𝒪1).obj.obj U)
    (s : (pushoutUnderlying E₂ k).obj.obj U) :
    pushoutSMul E₂ h h_comm k hc U (a + b) s =
      pushoutSMul E₂ h h_comm k hc U a s + pushoutSMul E₂ h h_comm k hc U b s := sorry

/-- The zero scalar acts by zero on the additive pushout. -/
theorem pushoutSMul_zero_smul (U : Cᵒᵖ) (s : (pushoutUnderlying E₂ k).obj.obj U) :
    pushoutSMul E₂ h h_comm k hc U 0 s = 0 := sorry

/-- The module structure on sections obtained by descending the local scalar formula. -/
@[reducible, expose] noncomputable def pushoutSectionModule (U : Cᵒᵖ) :
    Module ((ringSheaf J 𝒪1).obj.obj U) ((pushoutUnderlying E₂ k).obj.obj U) where
  smul := pushoutSMul E₂ h h_comm k hc U
  one_smul := pushoutSMul_one_smul E₂ h h_comm k hc U
  mul_smul := pushoutSMul_mul_smul E₂ h h_comm k hc U
  smul_zero := pushoutSMul_smul_zero E₂ h h_comm k hc U
  smul_add := pushoutSMul_smul_add E₂ h h_comm k hc U
  add_smul := pushoutSMul_add_smul E₂ h h_comm k hc U
  zero_smul := pushoutSMul_zero_smul E₂ h h_comm k hc U

/-- Restriction of pushout sections is semilinear for the descended scalar action. -/
theorem pushoutSMul_restrict {U V : Cᵒᵖ} (f : U ⟶ V)
    (a : (ringSheaf J 𝒪1).obj.obj U) (s : (pushoutUnderlying E₂ k).obj.obj U) :
    (pushoutUnderlying E₂ k).obj.map f (pushoutSMul E₂ h h_comm k hc U a s) =
      pushoutSMul E₂ h h_comm k hc V ((ringSheaf J 𝒪1).obj.map f a)
        ((pushoutUnderlying E₂ k).obj.map f s) := sorry

/-- The additive pushout equipped with the descended module structure over the target presentation. -/
@[expose] noncomputable def pushoutModule :
    ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪1 where
  val :=
    @PresheafOfModules.ofPresheaf C _ (ringSheaf J 𝒪1).obj
      (pushoutUnderlying E₂ k).obj
      (fun U ↦ pushoutSectionModule E₂ h h_comm k hc U)
      (fun {_ _} f a s ↦ pushoutSMul_restrict E₂ h h_comm k hc f a s)
  isSheaf := (pushoutUnderlying E₂ k).property

/-- The kernel leg of the additive pushout respects the target scalar action. -/
theorem pushoutIncl_smul (U : Cᵒᵖ) (a : (ringSheaf J 𝒪1).obj.obj U)
    (x : ((restrictionAlong π1).obj K1).val.obj U) :
    (pushoutInrSheaf E₂ k).hom.app U (a • x) =
      ((pushoutModule E₂ h h_comm k hc).val.obj U).isModule.smul a
        ((pushoutInrSheaf E₂ k).hom.app U x) := sorry

/-- The inclusion of the new kernel into the pushout module is its additive pushout leg. -/
@[expose] noncomputable def pushoutIncl :
    (restrictionAlong π1).obj K1 ⟶ pushoutModule E₂ h h_comm k hc where
  val := PresheafOfModules.homMk (pushoutInrSheaf E₂ k).hom
    (pushoutIncl_smul E₂ h h_comm k hc)

/-- The descended projection respects the target scalar action. -/
theorem pushoutProj_smul (U : Cᵒᵖ) (a : (ringSheaf J 𝒪1).obj.obj U)
    (s : (pushoutModule E₂ h h_comm k hc).val.obj U) :
    (projUnderlying E₂ k).hom.app U (a • s) =
      (((restrictionAlong π1).obj E₂.quot).val.obj U).isModule.smul a
        ((projUnderlying E₂ k).hom.app U s) := sorry

/-- The projection of the pushout module descends the original quotient map and the zero map. -/
@[expose] noncomputable def pushoutProj :
    pushoutModule E₂ h h_comm k hc ⟶ (restrictionAlong π1).obj E₂.quot where
  val := PresheafOfModules.homMk (projUnderlying E₂ k).hom
    (pushoutProj_smul E₂ h h_comm k hc)

/-- The inclusion and projection of the pushout module compose to zero. -/
theorem pushout_zero :
    pushoutIncl E₂ h h_comm k hc ≫ pushoutProj E₂ h h_comm k hc = 0 := sorry

/-- The new kernel, pushout module, and original quotient form a short exact sequence. -/
theorem pushout_shortExact :
    (ShortComplex.mk (pushoutIncl E₂ h h_comm k hc) (pushoutProj E₂ h h_comm k hc)
      (pushout_zero E₂ h h_comm k hc)).ShortExact := sorry

/-- The extension obtained by pushing out its kernel and changing the square-zero presentation. -/
@[expose] noncomputable def pushout : Extension π1 :=
  ofMaps π1 K1 (pushoutModule E₂ h h_comm k hc) E₂.quot
    (pushoutIncl E₂ h h_comm k hc) (pushoutProj E₂ h h_comm k hc)
    (pushout_zero E₂ h h_comm k hc) (pushout_shortExact E₂ h h_comm k hc)

/-- The infinitesimal action of the pushout is the restriction of the prescribed tensor map. -/
theorem pushout_restrictC_spec (U : Cᵒᵖ) (f : (KernelIdeal.sheaf π1).val.obj U)
    (s' : (pushout E₂ h h_comm k hc).middle.val.obj U) :
    ((pushout E₂ h h_comm k hc).ι.val.app U).hom
        (((moduleTensorMap (restrictIdealModuleIso hπ1).inv
              (𝟙 ((restrictionAlong π1).obj E₂.quot)) ≫
            Restriction.tensorComparison π1 (idealModule hπ1) E₂.quot ≫
            (restrictionAlong π1).map c1).val.app U).hom
          (tensorSection 𝒪1 U f (((pushout E₂ h h_comm k hc).p.val.app U).hom s'))) =
      KernelIdeal.ιApp π1 U f • s' := sorry

/-- The infinitesimal map of the constructed pushout is the prescribed tensor map. -/
theorem pushout_infMap_eq :
    infMap hπ1 (pushout E₂ h h_comm k hc) = c1 := sorry

/-- Forgetting the target action on the pushout module recovers the additive pushout. -/
theorem pushoutSheaf_toSheaf :
    (SheafOfModules.toSheaf (ringSheaf J 𝒪1)).obj (pushout E₂ h h_comm k hc).middle =
      pushoutUnderlying E₂ k := rfl

/-- The canonical additive legs form a pushout square. -/
theorem pushout_isPushout :
    IsPushout (inclUnderlying E₂) (kernelUnderlying k)
      (pushoutInlSheaf E₂ k) (pushoutInrSheaf E₂ k) :=
  IsPushout.of_hasPushout (inclUnderlying E₂) (kernelUnderlying k)

/-- The constructed extension has the prescribed endpoints and infinitesimal map, is short exact,
and has the canonical additive pushout as its middle sheaf. -/
theorem pushout_spec :
    (pushout E₂ h h_comm k hc).kernel = K1 ∧
      (pushout E₂ h h_comm k hc).quot = E₂.quot ∧
      (shortComplex (pushout E₂ h h_comm k hc)).ShortExact ∧
      infMap hπ1 (pushout E₂ h h_comm k hc) = c1 ∧
      IsPushout (inclUnderlying E₂) (kernelUnderlying k)
        (pushoutInlSheaf E₂ k) (pushoutInrSheaf E₂ k) :=
  ⟨rfl, rfl, (pushout E₂ h h_comm k hc).shortExact,
    pushout_infMap_eq E₂ h h_comm k hc, pushout_isPushout E₂ k⟩

end SheafOfModules.RingedSite.FirstOrderThickening.Extension
