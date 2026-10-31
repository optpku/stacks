/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Exact
import ReasLib.Algebra.Category.ModuleCat.Sheaf.OverSections
public import ReasLib.Topology.Sheaves.Abelian.Over
import Mathlib.Tactic.CrossRefAttribute

/-!
# Neighborhood properties of finite-type module sheaves

These statements live on a topological space equipped with an arbitrary sheaf of rings. Finite
type turns stalkwise surjectivity into a neighborhood epimorphism and stalkwise vanishing into
neighborhood vanishing. Applied to a kernel, the same vanishing criterion gives neighborhood
monomorphisms and, together with a finite-type target, neighborhood isomorphisms. The
commutative-ring specialization is only retained where its differently bundled stalk object
requires a bridge.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace SheafOfModules.IsFiniteType

/-- Direct image preserves finite limits because evaluation computes it by restriction of scalars. -/
private theorem restrictionPreservesFiniteLimits
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {T : C ⥤ D} [T.IsContinuous J K]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (ψ : S ⟶ (T.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{u} ψ) := by
  letI : PreservesFiniteLimits (SheafOfModules.pushforward.{u} ψ ⋙
      SheafOfModules.forget S) := by
    constructor
    intro A _ _
    constructor
    intro B
    constructor
    intro c hc
    refine ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun V => ?_)⟩
    exact isLimitOfPreserves
      (SheafOfModules.evaluation R (op (T.obj V.unop)) ⋙
        ModuleCat.restrictScalars (ψ.hom.app V).hom) hc
  exact preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.forget S)

variable {X : TopCat.{u}} {R : X.Sheaf RingCat.{u}}
variable {G F : SheafOfModules.{u} R}

set_option backward.isDefEq.respectTransparency false in
/-- A morphism to a finite-type module sheaf that is epic at a stalk is epic on some
neighborhood of that point. -/
@[stacks 01B8 "stalk epimorphism"]
theorem existsNeighborhood_epi (φ : G ⟶ F) (x : X) [F.IsFiniteType]
    (hφx : Epi ((SheafOfModules.stalkFunctor R x).map φ)) :
    ∃ (U : Opens X) (_ : x ∈ U), Epi (SheafOfModules.Hom.over φ U) := by
  classical
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  have hxcover : x ∈ iSup q.X := by
    rw [(Opens.coversTop_iff X q.X).1 q.coversTop]
    trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.1 hxcover
  let W := q.X i
  let σ := q.generators i
  letI := hq.isFiniteType i
  let s (j : σ.I) : F.val.obj (op W) := SheafOfModules.sectionsOverEquiv F W (σ.s j)
  -- Lift each generator near the point, then take a common finite intersection.
  have hlift (j : σ.I) : ∃ (V : Opens X) (hV : V ≤ W), x ∈ V ∧
      ∃ t : G.val.obj (op V), φ.val.app (op V) t = F.val.map (homOfLE hV).op (s j) := by
    obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective _).1 hφx
      (TopCat.Presheaf.germ F.val.presheaf W x hxi (s j))
    obtain ⟨A, hxA, t, ht⟩ := TopCat.Presheaf.exists_germ_eq G.val.presheaf a
    have heq : TopCat.Presheaf.germ F.val.presheaf A x hxA (φ.val.app (op A) t) =
        TopCat.Presheaf.germ F.val.presheaf W x hxi (s j) := by
      calc
        _ = ((SheafOfModules.stalkFunctor R x).map φ).hom
            (TopCat.Presheaf.germ G.val.presheaf A x hxA t) :=
          (TopCat.Presheaf.stalkFunctor_map_germ_apply A x hxA
            ((PresheafOfModules.toPresheaf R.obj).map φ.val) t).symm
        _ = _ := by
          rw [ht]
          exact ha
    obtain ⟨V, hxV, iA, iW, hV⟩ := TopCat.Presheaf.germ_eq F.val.presheaf x hxA hxi _ _ heq
    refine ⟨V, leOfHom iW, hxV, G.val.map iA.op t, ?_⟩
    exact (PresheafOfModules.naturality_apply φ.val iA.op t).trans hV
  choose V hVW hxV t ht using hlift
  let U := W ⊓ ⨅ j, V j
  have hxU : x ∈ U := by
    change x ∈ W ∧ x ∈ ⨅ j, V j
    refine ⟨hxi, ?_⟩
    change x ∈ ((⨅ j, V j : Opens X) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.2 hxV
  have hUW : U ≤ W := inf_le_left
  have hUV (j : σ.I) : U ≤ V j := inf_le_right.trans (iInf_le _ j)
  let D := SheafOfModules.overMap R (homOfLE hUW)
  let η := (SheafOfModules.overMapUnitIso (R := R) (homOfLE hUW)).symm
  let e := (SheafOfModules.overFunctorMap R (homOfLE hUW)).app F
  -- Restrict the generating epimorphism and factor it through the lifted sections.
  let π : SheafOfModules.free σ.I ⟶ F.over U :=
    (SheafOfModules.mapFreeIso D σ.I η).hom ≫ D.map σ.π ≫ e.hom
  have hπ (j : σ.I) :
      SheafOfModules.sectionsOverEquiv F U ((F.over U).freeHomEquiv π j) =
        F.val.map (homOfLE hUW).op (s j) := by
    have hι : SheafOfModules.ιFree j ≫ π =
        η.hom ≫ D.map ((F.over W).unitHomEquiv.symm (σ.s j)) ≫ e.hom := by
      dsimp only [π]
      rw [SheafOfModules.ιFree_mapFreeIso_hom_assoc, ← D.map_comp_assoc,
        ← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
      simp [SheafOfModules.GeneratingSections.π, W, σ]
    change (SheafOfModules.ιFree j ≫ π).val.app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U)) = _
    rw [hι]
    change ((F.over W).unitHomEquiv.symm (σ.s j)).val.app
      (op (Over.mk (homOfLE hUW))) (1 : R.obj.obj (op U)) = _
    rw [← SheafOfModules.unitHomEquiv_apply_coe, Equiv.apply_symm_apply]
    exact (PresheafOfModules.sections_property (σ.s j)
      (Over.homMk (homOfLE hUW) : Over.mk (homOfLE hUW) ⟶ Over.mk (𝟙 W)).op).symm
  let tU (j : σ.I) : (G.over U).sections :=
    (SheafOfModules.sectionsOverEquiv G U).symm (G.val.map (homOfLE (hUV j)).op (t j))
  have hfactor : (G.over U).freeHomEquiv.symm tU ≫ φ.over U = π := by
    apply (F.over U).freeHomEquiv.injective
    funext j
    rw [SheafOfModules.freeHomEquiv_comp_apply, Equiv.apply_symm_apply]
    apply (SheafOfModules.sectionsOverEquiv F U).injective
    rw [hπ]
    change φ.val.app (op U) (SheafOfModules.sectionsOverEquiv G U (tU j)) = _
    dsimp only [tU]
    rw [Equiv.apply_symm_apply]
    change φ.val.app (op U) (G.val.map (homOfLE (hUV j)).op (t j)) = _
    calc
      _ = F.val.map (homOfLE (hUV j)).op (φ.val.app (op (V j)) (t j)) :=
        PresheafOfModules.naturality_apply φ.val (homOfLE (hUV j)).op (t j)
      _ = F.val.map (homOfLE (hUV j)).op
          (F.val.map (homOfLE (hVW j)).op (s j)) := congrArg _ (ht j)
      _ = _ := by
        change (F.val.presheaf.map (homOfLE (hUV j)).op)
          (F.val.presheaf.map (homOfLE (hVW j)).op (s j)) = _
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl
  haveI : Epi π := by
    dsimp only [π]
    infer_instance
  refine ⟨U, hxU, ?_⟩
  haveI : Epi ((G.over U).freeHomEquiv.symm tU ≫ φ.over U) := by
    rw [hfactor]
    infer_instance
  exact epi_of_epi ((G.over U).freeHomEquiv.symm tU) (φ.over U)

/-- Surjectivity of a stalk map into a finite-type module sheaf extends to an epimorphism on
some neighborhood. -/
@[stacks 01B8]
theorem existsNeighborhood_epi_of_surjective (φ : G ⟶ F) (x : X) [F.IsFiniteType]
    (hφx : Function.Surjective
      (((SheafOfModules.stalkFunctor R x).map φ).hom)) :
    ∃ (U : Opens X) (_ : x ∈ U), Epi (SheafOfModules.Hom.over φ U) := by
  exact existsNeighborhood_epi φ x ((ModuleCat.epi_iff_surjective _).2 hφx)

/-- A finite-type module sheaf whose stalk is zero vanishes on some neighborhood of that
point. -/
@[stacks 01B9]
theorem existsNeighborhood_isZero
    (F : SheafOfModules.{u} R) (x : X) [F.IsFiniteType]
    (hFx : IsZero ((SheafOfModules.stalkFunctor R x).obj F)) :
    ∃ (U : Opens X) (_ : x ∈ U), IsZero (F.over U) := by
  obtain ⟨U, hxU, hU⟩ := existsNeighborhood_epi (0 : F ⟶ F) x (hFx.epi _)
  refine ⟨U, hxU, ?_⟩
  exact IsZero.of_epi_eq_zero (SheafOfModules.Hom.over (0 : F ⟶ F) U) rfl

/-- The commutative-ring-stalk formulation of neighborhood vanishing. This is a bridge to
`existsNeighborhood_isZero`, whose stalk is bundled over the underlying ring stalk. -/
@[stacks 01B9 "commutative-ring stalk bridge"]
theorem existsNeighborhood_isZeroOfCommRing
    {𝒪 : X.Sheaf CommRingCat.{u}}
    (F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪))
    (x : X) [F.IsFiniteType]
    (hFx : IsZero ((SheafOfModules.stalkFunctorOfCommRing 𝒪 x).obj F)) :
    ∃ (U : Opens X) (_ : x ∈ U), IsZero (F.over U) := by
  apply existsNeighborhood_isZero F x
  apply ModuleCat.isZero_iff_subsingleton.2
  exact ModuleCat.subsingleton_of_isZero
    (M := (SheafOfModules.stalkFunctorOfCommRing 𝒪 x).obj F) hFx

/-- Surjectivity of a commutative-ring stalk map into a finite-type module sheaf extends to an
epimorphism on some neighborhood. -/
theorem existsNeighborhood_epiOfCommRing_of_surjective
    {𝒪 : X.Sheaf CommRingCat.{u}}
    {G F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪)}
    (φ : G ⟶ F) (x : X) [F.IsFiniteType]
    (hφx : Function.Surjective
      (((SheafOfModules.stalkFunctorOfCommRing 𝒪 x).map φ).hom)) :
    ∃ (U : Opens X) (_ : x ∈ U), Epi (SheafOfModules.Hom.over φ U) := by
  exact existsNeighborhood_epi_of_surjective φ x hφx

end SheafOfModules.IsFiniteType

namespace SheafOfModules.Hom

variable {X : TopCat.{u}} {R : X.Sheaf RingCat.{u}}
variable {G F : SheafOfModules.{u} R}

/-- A morphism that is monic at a stalk is monic on some neighborhood whenever its kernel is
finite type. -/
@[stacks 01C0 "finite-type kernel criterion"]
theorem existsNeighborhood_mono (φ : G ⟶ F) (x : X)
    [(kernel φ).IsFiniteType]
    (hφx : Mono ((SheafOfModules.stalkFunctor R x).map φ)) :
    ∃ (U : Opens X) (_ : x ∈ U), Mono (SheafOfModules.Hom.over φ U) := by
  have hker : IsZero ((SheafOfModules.stalkFunctor R x).obj (kernel φ)) :=
    (isZero_kernel_of_mono ((SheafOfModules.stalkFunctor R x).map φ)).of_iso
      (PreservesKernel.iso (SheafOfModules.stalkFunctor R x) φ)
  obtain ⟨U, hxU, hU⟩ :=
    SheafOfModules.IsFiniteType.existsNeighborhood_isZero (kernel φ) x hker
  letI : PreservesFiniteLimits (SheafOfModules.overFunctor R U) :=
    SheafOfModules.IsFiniteType.restrictionPreservesFiniteLimits (𝟙 (R.over U))
  letI : Functor.PreservesZeroMorphisms (SheafOfModules.overFunctor R U) := ⟨fun _ _ => rfl⟩
  refine ⟨U, hxU, ?_⟩
  apply CategoryTheory.Preadditive.mono_of_isZero_kernel
  exact hU.of_iso (PreservesKernel.iso (SheafOfModules.overFunctor R U) φ).symm

set_option backward.isDefEq.respectTransparency false in
/-- A morphism that is an isomorphism at a stalk is an isomorphism on some neighborhood when
its kernel and target are finite type. -/
@[stacks 01Y3 "(4), categorical finite criterion"]
theorem existsNeighborhood_isIso (φ : G ⟶ F) (x : X)
    [(kernel φ).IsFiniteType] [F.IsFiniteType]
    (hφx : IsIso ((SheafOfModules.stalkFunctor R x).map φ)) :
    ∃ (U : Opens X) (_ : x ∈ U), IsIso (SheafOfModules.Hom.over φ U) := by
  obtain ⟨U, hxU, hU⟩ := SheafOfModules.Hom.existsNeighborhood_mono φ x (inferInstance)
  obtain ⟨V, hxV, hV⟩ := SheafOfModules.IsFiniteType.existsNeighborhood_epi φ x (inferInstance)
  have hmap (B : Opens X) {A : Opens X} (h : A ≤ B) :
      ((SheafOfModules.overFunctorMap R (homOfLE h)).app G).inv ≫
          (SheafOfModules.overMap R (homOfLE h)).map (φ.over B) ≫
          ((SheafOfModules.overFunctorMap R (homOfLE h)).app F).hom = φ.over A := by
    ext T t
    rfl
  letI : Mono (φ.over U) := hU
  letI : Epi (φ.over V) := hV
  haveI : Mono (φ.over (U ⊓ V)) := by
    rw [← hmap U inf_le_left]
    letI : PreservesFiniteLimits (SheafOfModules.overMap R
        (homOfLE (inf_le_left : U ⊓ V ≤ U))) :=
      SheafOfModules.IsFiniteType.restrictionPreservesFiniteLimits _
    haveI := (SheafOfModules.overMap R (homOfLE (inf_le_left : U ⊓ V ≤ U))).map_mono (φ.over U)
    infer_instance
  haveI : Epi (φ.over (U ⊓ V)) := by
    rw [← hmap V inf_le_right]
    haveI := (SheafOfModules.overMap R (homOfLE (inf_le_right : U ⊓ V ≤ V))).map_epi (φ.over V)
    infer_instance
  exact ⟨U ⊓ V, ⟨hxU, hxV⟩, isIso_of_mono_of_epi _⟩

/-- Bijectivity of a stalk map extends to an isomorphism on some neighborhood when the kernel
and target are finite type. -/
@[stacks 01Y3 "(4), finite criterion"]
theorem existsNeighborhood_isIso_of_bijective (φ : G ⟶ F) (x : X)
    [(kernel φ).IsFiniteType] [F.IsFiniteType]
    (hφx : Function.Bijective
      (((SheafOfModules.stalkFunctor R x).map φ).hom)) :
    ∃ (U : Opens X) (_ : x ∈ U), IsIso (SheafOfModules.Hom.over φ U) := by
  letI := (ModuleCat.mono_iff_injective ((SheafOfModules.stalkFunctor R x).map φ)).2 hφx.1
  letI := (ModuleCat.epi_iff_surjective ((SheafOfModules.stalkFunctor R x).map φ)).2 hφx.2
  exact existsNeighborhood_isIso φ x (isIso_of_mono_of_epi _)

/-- Bijectivity of a commutative-ring stalk map extends to an isomorphism on some neighborhood
when the kernel and target are finite type. -/
theorem existsNeighborhood_isIsoOfCommRing_of_bijective
    {𝒪 : X.Sheaf CommRingCat.{u}}
    {G F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪)}
    (φ : G ⟶ F) (x : X) [(kernel φ).IsFiniteType] [F.IsFiniteType]
    (hφx : Function.Bijective
      (((SheafOfModules.stalkFunctorOfCommRing 𝒪 x).map φ).hom)) :
    ∃ (U : Opens X) (_ : x ∈ U), IsIso (SheafOfModules.Hom.over φ U) := by
  exact existsNeighborhood_isIso_of_bijective φ x hφx

end SheafOfModules.Hom
