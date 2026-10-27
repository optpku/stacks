/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.ExtensionByInitial
public import ReasLib.Topology.Sheaf.Subset.Closed
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Tactic.CrossRefAttribute

/-!
# The canonical sequence for an open subset and its closed complement

For an open subset `U ⊆ X`, this file packages the canonical maps
`j_! j^{-1} F ⟶ F ⟶ i_* i^{-1} F` before evaluating them at an individual sheaf.
The resulting functor to `ShortComplex` makes functoriality in `F` part of the construction,
rather than a separate collection of naturality lemmas.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.OpenClosed

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-- The inclusion of the closed complement of an open subset. -/
abbrev complementInclusion (U : Opens X) :
    TopCat.subsetSpace ((U : Set X)ᶜ) ⟶ X :=
  TopCat.subsetInclusion ((U : Set X)ᶜ)

/-- Restriction to `U` followed by extension by zero back to `X`. -/
noncomputable def openPart (U : Opens X) :
    X.Sheaf AddCommGrpCat.{u} ⥤ X.Sheaf AddCommGrpCat.{u} :=
  TopCat.Sheaf.pullback AddCommGrpCat.{u} (TopCat.Opens.Subspace.inclusion U) ⋙
    TopCat.Sheaf.ExtensionByInitial.functor U

/-- Restriction to the closed complement of `U` followed by pushforward to `X`. -/
noncomputable def closedPart (U : Opens X) :
    X.Sheaf AddCommGrpCat.{u} ⥤ X.Sheaf AddCommGrpCat.{u} :=
  TopCat.Sheaf.pullback AddCommGrpCat.{u} (complementInclusion U) ⋙
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} (complementInclusion U)

/-- The counit `j_! j^{-1} ⟶ 𝟭` for the open part. -/
noncomputable def openCounit (U : Opens X) : openPart U ⟶ 𝟭 _ :=
  (TopCat.Sheaf.ExtensionByInitial.Properties.adjunction
    (C := AddCommGrpCat.{u}) U).counit

/-- The unit `𝟭 ⟶ i_* i^{-1}` for the closed part. -/
noncomputable def closedUnit (U : Opens X) : 𝟭 _ ⟶ closedPart U :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    (complementInclusion U)).unit

omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
set_option backward.isDefEq.respectTransparency false in
/-- A morphism of abelian sheaves vanishes if its stalk maps vanish. -/
private theorem hom_eq_zero_of_stalk_map_eq_zero {F G : X.Sheaf AddCommGrpCat.{u}}
    (φ : F ⟶ G)
    (h : ∀ x : X, (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ.hom = 0) :
    φ = 0 := by
  apply (TopCat.Sheaf.forget AddCommGrpCat.{u} X).map_injective
  ext V s
  change φ.hom.app (Opposite.op V) s = 0
  apply TopCat.Presheaf.section_ext G V _ _
  intro x hx
  rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply, h x]
  simp

/-- The open part has zero stalks outside the open subset. -/
private theorem open_stalk_zero (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u})
    (x : X) (hx : x ∉ (U : Set X)) :
    IsZero (((openPart U).obj F).presheaf.stalk x) := by
  change IsZero (((TopCat.Sheaf.ExtensionByInitial.functor U).obj
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (TopCat.Opens.Subspace.inclusion U)).obj F)).presheaf.stalk x)
  haveI := TopCat.Sheaf.ExtensionByInitial.Properties.stalk_isInitial_of_not_mem
    U ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (TopCat.Opens.Subspace.inclusion U)).obj F) x hx
  exact IsZero.of_epi_eq_zero (initial.to _)
    ((initialIsInitial.isZero (C := AddCommGrpCat.{u})).eq_of_src _ _)

omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
/-- The closed part has zero stalks on the open subset. -/
private theorem closed_stalk_zero (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u})
    (x : X) (hx : x ∈ (U : Set X)) :
    IsZero (((closedPart U).obj F).presheaf.stalk x) := by
  exact TopCat.Sheaf.ClosedSubset.AddCommGrp.stalk_isZero_of_not_mem U.isOpen.isClosed_compl
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (complementInclusion U)).obj F) x
    (by simpa using hx)

/-- The open counit followed by the closed unit is the zero natural transformation. -/
theorem comp_zero (U : Opens X) : openCounit U ≫ closedUnit U = 0 := by
  apply NatTrans.ext
  funext F
  apply hom_eq_zero_of_stalk_map_eq_zero
  intro x
  change (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((openCounit U).app F ≫ (closedUnit U).app F) = 0
  rw [Functor.map_comp]
  by_cases hx : x ∈ (U : Set X)
  · exact (closed_stalk_zero U F x hx).eq_of_tgt _ _
  · exact (open_stalk_zero U F x hx).eq_of_src _ _

/-- The open-closed sequence as a short complex in the endofunctor category. -/
noncomputable def diagram (U : Opens X) :
    ShortComplex (X.Sheaf AddCommGrpCat.{u} ⥤ X.Sheaf AddCommGrpCat.{u}) :=
  ShortComplex.mk (openCounit U) (closedUnit U) (comp_zero U)

/-- Lemma 17.7.1 (02UT) (2): the canonical open-closed short complex is functorial in the
abelian sheaf. -/
@[stacks 02UT "functorial canonical open-closed sequence"]
noncomputable def sequence (U : Opens X) :
    X.Sheaf AddCommGrpCat.{u} ⥤ ShortComplex (X.Sheaf AddCommGrpCat.{u}) :=
  (ShortComplex.functorEquivalence
    (X.Sheaf AddCommGrpCat.{u}) (X.Sheaf AddCommGrpCat.{u})).functor.obj (diagram U)

/-- The first object of the open-closed sequence is the open part. -/
@[simp]
theorem sequence_obj_X₁ (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    ((sequence U).obj F).X₁ = (openPart U).obj F := rfl

/-- The middle object of the open-closed sequence is the original sheaf. -/
@[simp]
theorem sequence_obj_X₂ (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    ((sequence U).obj F).X₂ = F := rfl

/-- The third object of the open-closed sequence is the closed part. -/
@[simp]
theorem sequence_obj_X₃ (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    ((sequence U).obj F).X₃ = (closedPart U).obj F := rfl

/-- The first differential of the open-closed sequence is the open counit. -/
@[simp]
theorem sequence_obj_f (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    ((sequence U).obj F).f = (openCounit U).app F := rfl

/-- The second differential of the open-closed sequence is the closed unit. -/
@[simp]
theorem sequence_obj_g (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    ((sequence U).obj F).g = (closedUnit U).app F := rfl

/-- On a sheaf morphism, the first component is obtained by applying the open-part functor. -/
@[simp]
theorem sequence_map_τ₁ (U : Opens X) {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) :
    ((sequence U).map f).τ₁ = (openPart U).map f := rfl

/-- On a sheaf morphism, the middle component is the original morphism. -/
@[simp]
theorem sequence_map_τ₂ (U : Opens X) {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) :
    ((sequence U).map f).τ₂ = f := rfl

/-- On a sheaf morphism, the third component is obtained by applying the closed-part functor. -/
@[simp]
theorem sequence_map_τ₃ (U : Opens X) {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) :
    ((sequence U).map f).τ₃ = (closedPart U).map f := rfl

omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
set_option backward.isDefEq.respectTransparency false in
/-- A pullback detects the stalk map at the image of a point. -/
private theorem stalk_isIso_of_pullback_map_isIso {Y : TopCat.{u}} (f : Y ⟶ X)
    {F G : X.Sheaf AddCommGrpCat.{u}} (φ : F ⟶ G)
    [IsIso ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map φ)] (x : Y) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map φ.hom) := by
  haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map φ).hom) :=
    Functor.map_isIso (TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) _
  haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map φ.hom ≫
      (TopCat.Sheaf.stalkPullbackIso f G x).hom) := by
    rw [TopCat.Sheaf.stalkPullbackIso_hom_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (TopCat.Sheaf.stalkPullbackIso f G x).hom

set_option backward.isDefEq.respectTransparency false in
/-- On the open subset, the counit is a stalkwise isomorphism by the right triangle identity. -/
private theorem open_counit_stalk_isIso (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u})
    (x : TopCat.Opens.Subspace.space U) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.val).map
      ((openCounit U).app F).hom) := by
  let adj := TopCat.Sheaf.ExtensionByInitial.Properties.adjunction
    (C := AddCommGrpCat.{u}) U
  haveI : IsIso ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (TopCat.Opens.Subspace.inclusion U)).map ((openCounit U).app F)) := by
    haveI : IsIso (adj.unit.app
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
          (TopCat.Opens.Subspace.inclusion U)).obj F)) :=
      (TopCat.Sheaf.ExtensionByInitial.Properties.unitIso U _).isIso_hom
    exact IsIso.of_isIso_fac_left (adj.right_triangle_components F)
  exact stalk_isIso_of_pullback_map_isIso (TopCat.Opens.Subspace.inclusion U) _ x

omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
set_option backward.isDefEq.respectTransparency false in
/-- On the closed complement, the unit is a stalkwise isomorphism by the left triangle identity. -/
private theorem closed_unit_stalk_isIso (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u})
    (x : TopCat.subsetSpace ((U : Set X)ᶜ)) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.val).map
      ((closedUnit U).app F).hom) := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    (complementInclusion U)
  haveI : IsIso ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (complementInclusion U)).map ((closedUnit U).app F)) := by
    haveI : IsIso (adj.counit.app
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (complementInclusion U)).obj F)) :=
      (by
        dsimp only [adj, complementInclusion]
        infer_instance)
    haveI : IsIso (𝟙 ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
        (complementInclusion U)).obj F)) := inferInstance
    exact IsIso.of_isIso_fac_right (adj.left_triangle_components F)
  exact stalk_isIso_of_pullback_map_isIso (complementInclusion U) _ x

/-- On each stalk, one differential is invertible and the opposite end object is zero. -/
private theorem stalk_shortExact (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (x : X) :
    (((sequence U).obj F).map (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).ShortExact := by
  let S := ((sequence U).obj F).map (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
  change S.ShortExact
  by_cases hx : x ∈ (U : Set X)
  · haveI : IsIso S.f := open_counit_stalk_isIso U F ⟨x, hx⟩
    have hz : IsZero S.X₃ := closed_stalk_zero U F x hx
    exact ShortComplex.ShortExact.mk'
      ((S.exact_iff_epi (hz.eq_of_tgt _ _)).2 inferInstance)
      inferInstance (hz.epi S.g)
  · haveI : IsIso S.g := closed_unit_stalk_isIso U F ⟨x, hx⟩
    have hz : IsZero S.X₁ := open_stalk_zero U F x hx
    exact ShortComplex.ShortExact.mk'
      ((S.exact_iff_mono (hz.eq_of_src _ _)).2 inferInstance)
      (hz.mono S.f) inferInstance

/-- Lemma 17.7.1 (02UT) (1): the canonical open-closed sequence of an abelian sheaf is short
exact. -/
@[stacks 02UT "canonical open-closed sequence is short exact"]
theorem shortExact (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    ((sequence U).obj F).ShortExact := by
  let S := (sequence U).obj F
  refine ShortComplex.ShortExact.mk'
    ((TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).2
      (fun x => (stalk_shortExact U F x).exact)) ?_ ?_
  · haveI (x : X) : Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.f.hom) :=
      (stalk_shortExact U F x).mono_f
    exact TopCat.Presheaf.mono_of_stalk_mono S.f
  · apply Preadditive.epi_of_cancel_zero
    intro G φ hφ
    apply hom_eq_zero_of_stalk_map_eq_zero
    intro x
    let T := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    haveI : Epi (T.map S.g) := (stalk_shortExact U F x).epi_g
    change T.map φ = 0
    apply zero_of_epi_comp (T.map S.g)
    rw [← T.map_comp, hφ, T.map_zero]

end TopCat.Sheaf.OpenClosed

end

end
