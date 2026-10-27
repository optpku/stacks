/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper.FiniteUnion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType
import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Exact
import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
import Mathlib.Topology.Sheaves.Abelian

/-!
# Proper support of scheme modules

This file packages the topological closure of a module support as a closed subset and records
properness of finite-type quasi-coherent support under base change and the standard abelian
operations.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- The canonical presentation equivalence is needed only inside the following proofs.
local instance properSupportToRingedSpaceIsEquivalence (X : Scheme.{u}) :
    (toRingedSpace X).IsEquivalence :=
  (ringedSpaceEquivalence X).isEquivalence_functor

local instance properSupportFromRingedSpaceIsEquivalence (X : Scheme.{u}) :
    (fromRingedSpace X).IsEquivalence :=
  (ringedSpaceEquivalence X).isEquivalence_inverse

/-- The closed support of a module on a scheme is the topological closure of its module support. -/
def closedSupport {X : Scheme.{u}} (ℱ : X.Modules) : TopologicalSpace.Closeds X :=
  TopologicalSpace.Closeds.closure (moduleSupport ℱ)

/-- The underlying set of the closed support is the module support. -/
@[simp]
theorem coe_closedSupport {X : Scheme.{u}} (ℱ : X.Modules)
    [ℱ.IsFiniteType] :
    (closedSupport ℱ : Set X) = moduleSupport ℱ := by
  rw [closedSupport, TopologicalSpace.Closeds.coe_closure,
    (isClosed_moduleSupport ℱ).closure_eq]

/-- Pullback carries the closed support of a finite-type quasi-coherent module to its inverse
image. -/
theorem closedSupport_pullback
    {X Y : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    (f : Y ⟶ X) :
    closedSupport ((Scheme.Modules.pullback f).obj ℱ) =
      (closedSupport ℱ).preimage f.continuous := by
  apply SetLike.coe_injective
  simpa only [coe_closedSupport, TopologicalSpace.Closeds.coe_preimage] using
    moduleSupport_pullback_eq_preimage ℱ f

/-- In a cartesian square, pullback preserves properness over the base of the closed support of a
finite-type quasi-coherent module. -/
theorem closedSupport_pullback_isProperOver
    {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} (sq : IsPullback g' f' f g)
    [LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [ClosedSubset.IsProperOver f (closedSupport ℱ)] :
    ClosedSubset.IsProperOver f' (closedSupport ((Scheme.Modules.pullback g').obj ℱ)) := by
  rw [closedSupport_pullback]
  exact ClosedSubset.IsProperOver.preimage sq (closedSupport ℱ)

/-- A module on `X` has proper support over `f : X ⟶ S` when its support is closed and the
corresponding reduced closed subscheme is proper over `S`. -/
class HasProperSupportOver {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) : Prop where
  /-- The support of the module is closed. -/
  isClosed_moduleSupport : IsClosed (moduleSupport ℱ)
  /-- The reduced closed subscheme on the support is proper over the base. -/
  isProper_moduleSupport :
    ClosedSubset.IsProperOver f
      (⟨moduleSupport ℱ, isClosed_moduleSupport⟩ : TopologicalSpace.Closeds X)

/-- A finite-type module has proper support when its canonical closed support is proper. -/
instance instHasProperSupportOverOfClosedSupportIsProper
    {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
    [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [ClosedSubset.IsProperOver f (closedSupport ℱ)] :
    HasProperSupportOver f ℱ :=
  ⟨isClosed_moduleSupport ℱ, by
    have h :
        (⟨moduleSupport ℱ, isClosed_moduleSupport ℱ⟩ : TopologicalSpace.Closeds X) =
          closedSupport ℱ := by
      apply SetLike.coe_injective
      exact (coe_closedSupport ℱ).symm
    rw [h]
    infer_instance⟩

/-- Proper support gives properness of the reduced closed subscheme on the module support. -/
theorem HasProperSupportOver.isProper
    {X S : Scheme.{u}} {f : X ⟶ S} {ℱ : X.Modules} [h : HasProperSupportOver f ℱ] :
    ClosedSubset.IsProperOver f
      (⟨moduleSupport ℱ, h.isClosed_moduleSupport⟩ : TopologicalSpace.Closeds X) :=
  h.isProper_moduleSupport

/-- Having proper support is equivalent to closedness of the support together with properness of
its reduced closed subscheme over the base. -/
theorem hasProperSupportOver_iff
    {X S : Scheme.{u}} {f : X ⟶ S} {ℱ : X.Modules} :
    HasProperSupportOver f ℱ ↔
      ∃ hclosed : IsClosed (moduleSupport ℱ),
        ClosedSubset.IsProperOver f
          (⟨moduleSupport ℱ, hclosed⟩ : TopologicalSpace.Closeds X) := by
  constructor
  · intro h
    exact ⟨h.isClosed_moduleSupport, h.isProper_moduleSupport⟩
  · rintro ⟨hclosed, hproper⟩
    exact ⟨hclosed, hproper⟩

/-- A finite-type quasi-coherent module whose support is contained in a proper module support
also has proper support. -/
theorem HasProperSupportOver.of_subset
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {ℱ 𝒢 : X.Modules} [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [HasProperSupportOver f 𝒢]
    (h : moduleSupport ℱ ⊆ moduleSupport 𝒢) :
    HasProperSupportOver f ℱ := by
  refine ⟨Scheme.Modules.isClosed_moduleSupport ℱ, ?_⟩
  exact ClosedSubset.IsProperOver.mono h (hZ := HasProperSupportOver.isProper)

-- Pin the site and topological sheaf category instances in the exact stalk functor.
private theorem properSupport_stalk_preservesFiniteLimits (X : Scheme.{u}) (x : X) :
    PreservesFiniteLimits
      (toRingedSpace X ⋙ SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙
        (sheafToPresheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u} ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)) := by
  have h := @comp_preservesFiniteLimits _ _ _ _ _ _
    (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
    (sheafToPresheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u} ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
    (inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf)))
    (inferInstanceAs (PreservesFiniteLimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)))
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _
    (inferInstanceAs (PreservesFiniteLimits (toRingedSpace X))) h

private theorem properSupport_stalk_preservesFiniteColimits (X : Scheme.{u}) (x : X) :
    PreservesFiniteColimits
      (toRingedSpace X ⋙ SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙
        (sheafToPresheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u} ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)) := by
  have h := @comp_preservesFiniteColimits _ _ _ _ _ _
    (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
    (sheafToPresheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u} ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
    (inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf)))
    (inferInstanceAs (PreservesFiniteColimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)))
  exact @comp_preservesFiniteColimits _ _ _ _ _ _ _ _
    (inferInstanceAs (PreservesFiniteColimits (toRingedSpace X))) h

private theorem moduleSupport_subset_of_mono
    {X : Scheme.{u}} {ℱ 𝒢 : X.Modules} (i : ℱ ⟶ 𝒢) [Mono i] :
    moduleSupport ℱ ⊆ moduleSupport 𝒢 := by
  intro x hx
  let T : X.Modules ⥤ AddCommGrpCat.{u} := toRingedSpace X ⋙
    SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙
    ((sheafToPresheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
  haveI : PreservesFiniteLimits T := properSupport_stalk_preservesFiniteLimits X x
  change ¬ IsZero (T.obj ℱ) at hx
  change ¬ IsZero (T.obj 𝒢)
  haveI : Mono (T.map i) := Functor.map_mono T i
  exact fun h ↦ hx (IsZero.of_mono (T.map i) h)

private theorem moduleSupport_subset_of_epi
    {X : Scheme.{u}} {ℱ 𝒢 : X.Modules} (q : ℱ ⟶ 𝒢) [Epi q] :
    moduleSupport 𝒢 ⊆ moduleSupport ℱ := by
  intro x hx
  let T : X.Modules ⥤ AddCommGrpCat.{u} := toRingedSpace X ⋙
    SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙
    ((sheafToPresheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
  haveI : PreservesFiniteColimits T := properSupport_stalk_preservesFiniteColimits X x
  change ¬ IsZero (T.obj 𝒢) at hx
  change ¬ IsZero (T.obj ℱ)
  haveI : Epi (T.map q) := Functor.map_epi T q
  exact fun h ↦ hx (IsZero.of_epi (T.map q) h)

private theorem hasProperSupportOver_of_subset_union
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {ℱ 𝒢 ℋ : X.Modules} [ℱ.IsFiniteType]
    [h𝒢 : HasProperSupportOver f 𝒢] [hℋ : HasProperSupportOver f ℋ]
    (h : moduleSupport ℱ ⊆ moduleSupport 𝒢 ∪ moduleSupport ℋ) :
    HasProperSupportOver f ℱ := by
  let Z : ULift.{u} Bool → TopologicalSpace.Closeds X := fun b ↦
    if b.down then ⟨moduleSupport 𝒢, h𝒢.isClosed_moduleSupport⟩
    else ⟨moduleSupport ℋ, hℋ.isClosed_moduleSupport⟩
  have hproper : ∀ b, ClosedSubset.IsProperOver f (Z b) := by
    rintro ⟨b⟩
    cases b
    · exact hℋ.isProper_moduleSupport
    · exact h𝒢.isProper_moduleSupport
  letI := ClosedSubset.IsProperOver.iSup f Z hproper
  refine ⟨isClosed_moduleSupport ℱ, ?_⟩
  apply ClosedSubset.IsProperOver.mono (Z := iSup Z)
  intro x hx
  rcases h hx with hx | hx
  · exact (le_iSup Z ⟨true⟩) hx
  · exact (le_iSup Z ⟨false⟩) hx

private theorem moduleSupport_middle_subset_union
    {X : Scheme.{u}} {C : ShortComplex X.Modules} (hC : C.ShortExact) :
    moduleSupport C.X₂ ⊆ moduleSupport C.X₁ ∪ moduleSupport C.X₃ := by
  haveI := hC.mono_f
  haveI := hC.epi_g
  intro x hx
  let T : X.Modules ⥤ AddCommGrpCat.{u} := toRingedSpace X ⋙
    SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙
    ((sheafToPresheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
  haveI : PreservesFiniteLimits T := properSupport_stalk_preservesFiniteLimits X x
  haveI : PreservesFiniteColimits T := properSupport_stalk_preservesFiniteColimits X x
  change ¬ IsZero (T.obj C.X₂) at hx
  change ¬ IsZero (T.obj C.X₁) ∨ ¬ IsZero (T.obj C.X₃)
  by_contra h
  push Not at h
  exact hx ((hC.map T).exact.isZero_of_both_isZero h.1 h.2)

/-- The biproduct of two finite-type quasi-coherent modules with proper support has proper
support. -/
theorem HasProperSupportOver.biprod
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ 𝒢 : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [𝒢.IsFiniteType] [𝒢.IsQuasicoherent]
    [HasProperSupportOver f ℱ] [HasProperSupportOver f 𝒢] :
    HasProperSupportOver f (ℱ ⊞ 𝒢) := by
  have hC := (ShortComplex.Splitting.ofHasBinaryBiproduct ℱ 𝒢).shortExact
  letI : (ℱ ⊞ 𝒢).IsFiniteType :=
    @SheafOfModules.isFiniteType_of_shortExact.{u} _ _ _ _ _ _ _ _ _ _
      (hC.map (toRingedSpace X)) ‹ℱ.IsFiniteType› ‹𝒢.IsFiniteType›
  exact hasProperSupportOver_of_subset_union f (moduleSupport_middle_subset_union hC)

/-- In a short exact sequence of finite-type quasi-coherent modules, proper support of the outer
terms implies proper support of the middle term. -/
theorem HasProperSupportOver.middle_of_shortExact
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (C : ShortComplex X.Modules)
    [C.X₁.IsFiniteType] [C.X₁.IsQuasicoherent]
    [C.X₃.IsFiniteType] [C.X₃.IsQuasicoherent]
    [HasProperSupportOver f C.X₁] [HasProperSupportOver f C.X₃]
    (hC : C.ShortExact) :
    HasProperSupportOver f C.X₂ := by
  haveI := hC.mono_f
  haveI := hC.epi_g
  letI : C.X₂.IsFiniteType :=
    @SheafOfModules.isFiniteType_of_shortExact.{u} _ _ _ _ _ _ _ _ _ _
      (hC.map (toRingedSpace X)) ‹C.X₁.IsFiniteType› ‹C.X₃.IsFiniteType›
  exact hasProperSupportOver_of_subset_union f (moduleSupport_middle_subset_union hC)

/-- A quasi-coherent quotient of a finite-type quasi-coherent module with proper support has
proper support. -/
theorem HasProperSupportOver.of_epi
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {ℱ Q : X.Modules} [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [Q.IsQuasicoherent] [HasProperSupportOver f ℱ]
    (q : ℱ ⟶ Q) [Epi q] :
    HasProperSupportOver f Q := by
  letI : Q.IsFiniteType :=
    @SheafOfModules.isFiniteType_of_epi.{u} _ _ _ _ _ _ _ _ _ _ _ _ _
      ((toRingedSpace X).map q) (Functor.map_epi (toRingedSpace X) q) ‹ℱ.IsFiniteType›
  exact HasProperSupportOver.of_subset f (moduleSupport_subset_of_epi q)

/-- The image of a morphism between finite-type quasi-coherent modules with proper support has
proper support. -/
theorem HasProperSupportOver.image
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ 𝒢 : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [𝒢.IsFiniteType] [𝒢.IsQuasicoherent]
    [HasProperSupportOver f ℱ] [HasProperSupportOver f 𝒢]
    (u : ℱ ⟶ 𝒢) :
    HasProperSupportOver f (Abelian.image u) := by
  letI : (Abelian.image u).IsQuasicoherent :=
    (Scheme.quasiCoherentModuleProperty X).prop_of_iso (Abelian.coimageIsoImage u)
      (show (Abelian.coimage u).IsQuasicoherent from inferInstance)
  exact HasProperSupportOver.of_epi f (Abelian.factorThruImage u)

/-- The cokernel of a morphism between finite-type quasi-coherent modules with proper support has
proper support. -/
theorem HasProperSupportOver.cokernel
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ 𝒢 : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [𝒢.IsFiniteType] [𝒢.IsQuasicoherent]
    [HasProperSupportOver f ℱ] [HasProperSupportOver f 𝒢]
    (u : ℱ ⟶ 𝒢) :
    HasProperSupportOver f (cokernel u) := by
  exact HasProperSupportOver.of_epi f (cokernel.π u)

/-- On a scheme locally of finite type over a locally Noetherian base, coherent modules with
proper support form a Serre class. -/
instance coherent_hasProperSupportOver_isSerreClass
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [AlgebraicGeometry.IsLocallyNoetherian S] :
    ObjectProperty.IsSerreClass
      ((fun ℱ : RingedSpace.Coh X.toRingedSpace ↦ HasProperSupportOver f ℱ.obj) :
        ObjectProperty (RingedSpace.Coh X.toRingedSpace)) := by
  letI := LocallyOfFiniteType.isLocallyNoetherian f
  let ι : RingedSpace.Coh X.toRingedSpace ⥤ X.Modules :=
    (SheafOfModules.isCoherent X.ringCatSheaf).ι ⋙ fromRingedSpace X
  haveI : PreservesFiniteLimits ι := comp_preservesFiniteLimits _ _
  haveI : PreservesFiniteColimits ι := comp_preservesFiniteColimits _ _
  have hft (ℱ : RingedSpace.Coh X.toRingedSpace) : ℱ.obj.IsFiniteType :=
    ℱ.property.toIsFiniteType
  have hqc (ℱ : RingedSpace.Coh X.toRingedSpace) : ℱ.obj.IsQuasicoherent :=
    ((isCoherent_iff_isQuasicoherent_and_isFiniteType ℱ.obj).mp ℱ.property).1
  refine
    { exists_zero := ?_
      prop_of_mono := ?_
      prop_of_epi := ?_
      prop_X₂_of_shortExact := ?_ }
  · refine ⟨0, isZero_zero _, ?_⟩
    let ℱ : RingedSpace.Coh X.toRingedSpace := 0
    change HasProperSupportOver f ℱ.obj
    have hz : IsZero (ι.obj ℱ) := ι.map_isZero (isZero_zero _)
    have hs : moduleSupport ℱ.obj = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      let T : X.Modules ⥤ AddCommGrpCat.{u} := toRingedSpace X ⋙
        SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙
        ((sheafToPresheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}) ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
      haveI : PreservesFiniteLimits T := properSupport_stalk_preservesFiniteLimits X x
      exact hx (T.map_isZero hz)
    have hp : ClosedSubset.IsProperOver f (⊥ : TopologicalSpace.Closeds X) := by
      simpa only [iSup_of_empty] using ClosedSubset.IsProperOver.iSup f
        (fun i : PEmpty.{u + 1} ↦ i.elim) (fun i ↦ i.elim)
    have hc : IsClosed (moduleSupport ℱ.obj) := by rw [hs]; exact isClosed_empty
    refine ⟨hc, ?_⟩
    have he : (⟨moduleSupport ℱ.obj, hc⟩ : TopologicalSpace.Closeds X) = ⊥ :=
      SetLike.coe_injective hs
    rw [he]
    exact hp
  · intro ℱ 𝒢 i hi h𝒢
    haveI := hi
    haveI : Mono (ι.map i) := Functor.map_mono ι i
    letI : HasProperSupportOver f (ι.obj 𝒢) := h𝒢
    letI : (ι.obj ℱ).IsFiniteType := hft ℱ
    letI : (ι.obj ℱ).IsQuasicoherent := hqc ℱ
    exact HasProperSupportOver.of_subset f
      (@moduleSupport_subset_of_mono X (ι.obj ℱ) (ι.obj 𝒢) (ι.map i)
        (Functor.map_mono ι i))
  · intro ℱ 𝒢 q hq hℱ
    haveI := hq
    haveI : Epi (ι.map q) := Functor.map_epi ι q
    letI : HasProperSupportOver f (ι.obj ℱ) := hℱ
    letI : (ι.obj ℱ).IsFiniteType := hft ℱ
    letI : (ι.obj ℱ).IsQuasicoherent := hqc ℱ
    letI : (ι.obj 𝒢).IsQuasicoherent := hqc 𝒢
    exact HasProperSupportOver.of_epi f (ℱ := ι.obj ℱ) (Q := ι.obj 𝒢) (ι.map q)
  · intro C hC h₁ h₃
    haveI := hC.mono_f
    haveI := hC.epi_g
    letI : HasProperSupportOver f (C.map ι).X₁ := h₁
    letI : HasProperSupportOver f (C.map ι).X₃ := h₃
    letI : (C.map ι).X₁.IsFiniteType := hft C.X₁
    letI : (C.map ι).X₃.IsFiniteType := hft C.X₃
    letI : (C.map ι).X₁.IsQuasicoherent := hqc C.X₁
    letI : (C.map ι).X₃.IsQuasicoherent := hqc C.X₃
    exact HasProperSupportOver.middle_of_shortExact f (C.map ι) (hC.map ι)

end AlgebraicGeometry.Scheme.Modules
