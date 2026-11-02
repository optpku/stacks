/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Basic
public import ReasLib.CategoryTheory.Sites.Sigma
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Types.Limits

@[expose] public section

universe w v u v' u'

namespace CategoryTheory.Limits.FormalCoproduct.Over

open Opposite Functor

private theorem sigma_isSheaf_of_components {I : Type*} {D : I → Type*}
    [∀ i, Category (D i)] (T : ∀ i, GrothendieckTopology (D i))
    (P : (Σ i, D i)ᵒᵖ ⥤ Type*)
    (hP : ∀ i, Presieve.IsSheaf (T i) ((CategoryTheory.Sigma.incl i).op ⋙ P)) :
    Presieve.IsSheaf (CategoryTheory.Sigma.topology T) P := by
  rintro ⟨i, U⟩ S hS x hx
  change S.functorPullback (CategoryTheory.Sigma.incl i) ∈ T i U at hS
  let y : Presieve.FamilyOfElements ((CategoryTheory.Sigma.incl i).op ⋙ P)
      (S.functorPullback (CategoryTheory.Sigma.incl i)).arrows :=
    fun V g hg => x ((CategoryTheory.Sigma.incl i).map g) hg
  have hy : y.Compatible := by
    intro V W Z p q g h hg hh hpq
    exact hx ((CategoryTheory.Sigma.incl i).map p) ((CategoryTheory.Sigma.incl i).map q)
      hg hh (congrArg (CategoryTheory.Sigma.incl i).map hpq)
  obtain ⟨t, ht, hut⟩ := hP i _ hS y hy
  refine ⟨t, ?_, ?_⟩
  · intro V g hg
    cases g with
    | mk g => exact ht g hg
  · intro t' ht'
    exact hut t' (fun V g hg => ht' ((CategoryTheory.Sigma.incl i).map g) hg)

private theorem sigma_incl_isContinuous {I : Type*} {D : I → Type*}
    [∀ i, Category (D i)] (T : ∀ i, GrothendieckTopology (D i)) (i : I) :
    (CategoryTheory.Sigma.incl i).IsContinuous (T i) (CategoryTheory.Sigma.topology T) := by
  apply Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfDownwardsClosed _ _ ?_) ?_
  · intro U V g
    cases g with
    | mk g => exact ⟨_, Iso.refl _⟩
  · constructor
    intro U S hS
    change (S.functorPushforward (CategoryTheory.Sigma.incl i)).functorPullback
      (CategoryTheory.Sigma.incl i) ∈ T i U
    simpa only [Sieve.functorPullback_functorPushforward_eq] using hS

variable {C : Type u} [Category.{v} C] {X : C}

/-- The localization category of a formal coproduct of objects over a fixed target. -/
abbrev Site (K : FormalCoproduct.{w} (CategoryTheory.Over X)) :=
  Σ i : K.I, CategoryTheory.Over (K.obj i).left

/-- The localization topology of a family is the disjoint union of its slice topologies. -/
def topology (J : GrothendieckTopology C) (K : FormalCoproduct.{w} (CategoryTheory.Over X)) :
    GrothendieckTopology (Site K) :=
  CategoryTheory.Sigma.topology fun i => J.over (K.obj i).left

/-- Localization composes each arrow to a family component with its arrow to the target. -/
def localization (K : FormalCoproduct.{w} (CategoryTheory.Over X)) :
    Site K ⥤ CategoryTheory.Over X :=
  CategoryTheory.Sigma.desc fun i => CategoryTheory.Over.map (K.obj i).hom

/-- Localization sends a component object to the composite arrow to the fixed target. -/
theorem localization_obj (K : FormalCoproduct.{w} (CategoryTheory.Over X))
    (i : K.I) (U : CategoryTheory.Over (K.obj i).left) :
    (localization K).obj ⟨i, U⟩ = CategoryTheory.Over.mk (U.hom ≫ (K.obj i).hom) := by
  rfl

/-- The family localization functor is continuous for the slice topologies. -/
instance localization_isContinuous (J : GrothendieckTopology C)
    (K : FormalCoproduct.{w} (CategoryTheory.Over X)) :
    (localization K).IsContinuous (topology J K) (J.over X) where
  op_comp_isSheaf_of_types F := by
    apply sigma_isSheaf_of_components
    intro i
    exact (CategoryTheory.Over.map (K.obj i).hom).op_comp_isSheaf_of_types
      (J.over (K.obj i).left) (J.over X) F

/-- The family localization functor is cocontinuous for the slice topologies. -/
instance localization_isCocontinuous (J : GrothendieckTopology C)
    (K : FormalCoproduct.{w} (CategoryTheory.Over X)) :
    (localization K).IsCocontinuous (topology J K) (J.over X) where
  cover_lift {U} S hS := by
    rcases U with ⟨i, U⟩
    exact (CategoryTheory.Over.map (K.obj i).hom).cover_lift
      (J.over (K.obj i).left) (J.over X) hS

variable {K L : FormalCoproduct.{w} (CategoryTheory.Over X)}

/-- A family morphism induces component relocalization together with its index function. -/
def siteMap (f : K ⟶ L) : Site K ⥤ Site L :=
  CategoryTheory.Sigma.desc fun i =>
    CategoryTheory.Over.map (f.φ i).left ⋙
      CategoryTheory.Sigma.incl (C := fun j : L.I => CategoryTheory.Over (L.obj j).left) (f.f i)

/-- The site map uses the family index function and composes with its component arrow. -/
theorem siteMap_obj (f : K ⟶ L) (i : K.I) (U : CategoryTheory.Over (K.obj i).left) :
    (siteMap f).obj ⟨i, U⟩ = ⟨f.f i, CategoryTheory.Over.mk (U.hom ≫ (f.φ i).left)⟩ := by
  rfl

/-- The site map induced by a family morphism is continuous. -/
instance siteMap_isContinuous (J : GrothendieckTopology C) (f : K ⟶ L) :
    (siteMap f).IsContinuous (topology J K) (topology J L) where
  op_comp_isSheaf_of_types F := by
    apply sigma_isSheaf_of_components
    intro i
    letI : (CategoryTheory.Sigma.incl
        (C := fun j : L.I => CategoryTheory.Over (L.obj j).left) (f.f i)).IsContinuous
        (J.over (L.obj (f.f i)).left) (topology J L) :=
      sigma_incl_isContinuous
        (fun j : L.I => J.over (L.obj j).left) (f.f i)
    letI := Functor.isContinuous_comp (CategoryTheory.Over.map (f.φ i).left)
      (CategoryTheory.Sigma.incl
        (C := fun j : L.I => CategoryTheory.Over (L.obj j).left) (f.f i))
      (J.over (K.obj i).left)
      (J.over (L.obj (f.f i)).left) (topology J L)
    exact Functor.op_comp_isSheaf_of_types (CategoryTheory.Over.map (f.φ i).left ⋙
      CategoryTheory.Sigma.incl
        (C := fun j : L.I => CategoryTheory.Over (L.obj j).left) (f.f i))
      (J.over (K.obj i).left) (topology J L) F

/-- The site map induced by a family morphism is cocontinuous. -/
instance siteMap_isCocontinuous (J : GrothendieckTopology C) (f : K ⟶ L) :
    (siteMap f).IsCocontinuous (topology J K) (topology J L) where
  cover_lift {U} S hS := by
    rcases U with ⟨i, U⟩
    exact (CategoryTheory.Over.map (f.φ i).left).cover_lift
      (J.over (K.obj i).left) (J.over (L.obj (f.f i)).left) hS

/-- Sheaves on a family localization are equivalent to families of sheaves on its component slices. -/
def sheafEquiv (J : GrothendieckTopology C) (K : FormalCoproduct.{w} (CategoryTheory.Over X))
    (A : Type u') [Category.{v'} A] :
    Sheaf (topology J K) A ≌ ∀ i : K.I, Sheaf (J.over (K.obj i).left) A :=
  CategoryTheory.Sigma.sheafEquiv (fun i => J.over (K.obj i).left) A

/-- The componentwise comparison from iterated slices over a target to slices over the sources. -/
def iteratedForward (K : FormalCoproduct.{w} (CategoryTheory.Over X)) :
    (Σ i : K.I, CategoryTheory.Over (K.obj i)) ⥤ Site K :=
  CategoryTheory.Sigma.desc fun i =>
    (K.obj i).iteratedSliceEquiv.functor ⋙
      CategoryTheory.Sigma.incl (C := fun j : K.I => CategoryTheory.Over (K.obj j).left) i

/-- The componentwise inverse comparison from source slices to iterated slices over a target. -/
def iteratedBackward (K : FormalCoproduct.{w} (CategoryTheory.Over X)) :
    Site K ⥤ Σ i : K.I, CategoryTheory.Over (K.obj i) :=
  CategoryTheory.Sigma.desc fun i =>
    (K.obj i).iteratedSliceEquiv.inverse ⋙
      CategoryTheory.Sigma.incl (C := fun j : K.I => CategoryTheory.Over (K.obj j)) i

/-- The iterated-slice unit on the disjoint union is induced by the canonical component units. -/
def iteratedUnitIso (K : FormalCoproduct.{w} (CategoryTheory.Over X)) :
    𝟭 (Σ i : K.I, CategoryTheory.Over (K.obj i)) ≅ iteratedForward K ⋙ iteratedBackward K :=
  let sourceIncl :=
    CategoryTheory.Sigma.incl (C := fun j : K.I => CategoryTheory.Over (K.obj j).left)
  let iteratedIncl :=
    CategoryTheory.Sigma.incl (C := fun j : K.I => CategoryTheory.Over (K.obj j))
  let forwardComponents := fun i => (K.obj i).iteratedSliceEquiv.functor ⋙ sourceIncl i
  let backwardComponents := fun i => (K.obj i).iteratedSliceEquiv.inverse ⋙ iteratedIncl i
  CategoryTheory.Sigma.natIso fun i =>
    (iteratedIncl i).rightUnitor ≪≫ (iteratedIncl i).leftUnitor.symm ≪≫
      isoWhiskerRight (K.obj i).iteratedSliceEquiv.unitIso (iteratedIncl i) ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (K.obj i).iteratedSliceEquiv.functor
        (CategoryTheory.Sigma.inclDesc backwardComponents i).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (CategoryTheory.Sigma.inclDesc forwardComponents i).symm
        (iteratedBackward K) ≪≫ Functor.associator _ _ _

/-- The iterated-slice counit on the disjoint union is induced by the canonical component counits. -/
def iteratedCounitIso (K : FormalCoproduct.{w} (CategoryTheory.Over X)) :
    iteratedBackward K ⋙ iteratedForward K ≅ 𝟭 (Site K) :=
  let sourceIncl :=
    CategoryTheory.Sigma.incl (C := fun j : K.I => CategoryTheory.Over (K.obj j).left)
  let iteratedIncl :=
    CategoryTheory.Sigma.incl (C := fun j : K.I => CategoryTheory.Over (K.obj j))
  let forwardComponents := fun i => (K.obj i).iteratedSliceEquiv.functor ⋙ sourceIncl i
  let backwardComponents := fun i => (K.obj i).iteratedSliceEquiv.inverse ⋙ iteratedIncl i
  CategoryTheory.Sigma.natIso fun i =>
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (CategoryTheory.Sigma.inclDesc backwardComponents i)
        (iteratedForward K) ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (K.obj i).iteratedSliceEquiv.inverse
        (CategoryTheory.Sigma.inclDesc forwardComponents i) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (K.obj i).iteratedSliceEquiv.counitIso (sourceIncl i) ≪≫
      (sourceIncl i).leftUnitor ≪≫ (sourceIncl i).rightUnitor.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The componentwise iterated-slice comparison satisfies the triangle identity. -/
theorem iteratedSiteEquiv_triangle (K : FormalCoproduct.{w} (CategoryTheory.Over X))
    (U : Σ i : K.I, CategoryTheory.Over (K.obj i)) :
    (iteratedForward K).map ((iteratedUnitIso K).hom.app U) ≫
      (iteratedCounitIso K).hom.app ((iteratedForward K).obj U) =
        𝟙 ((iteratedForward K).obj U) := by
  rcases U with ⟨i, U⟩
  have h := congrArg (CategoryTheory.Sigma.incl
    (C := fun j : K.I => CategoryTheory.Over (K.obj j).left) i).map
    ((K.obj i).iteratedSliceEquiv.functor_unitIso_comp U)
  simp +instances [iteratedForward, iteratedBackward, iteratedUnitIso, iteratedCounitIso,
    CategoryTheory.Sigma.natIso, CategoryTheory.Sigma.natTrans] at h ⊢
  exact h

/-- Iterated family slices and the disjoint union of source slices are canonically equivalent. -/
def iteratedSiteEquiv (K : FormalCoproduct.{w} (CategoryTheory.Over X)) :
    (Σ i : K.I, CategoryTheory.Over (K.obj i)) ≌ Site K where
  functor := iteratedForward K
  inverse := iteratedBackward K
  unitIso := iteratedUnitIso K
  counitIso := iteratedCounitIso K
  functor_unitIso_comp := iteratedSiteEquiv_triangle K

/-- The iterated-slice comparison identifies the iterated slice topology with the source topology. -/
theorem iteratedSite_mem_topology_iff (J : GrothendieckTopology C)
    (K : FormalCoproduct.{w} (CategoryTheory.Over X))
    (U : Σ i : K.I, CategoryTheory.Over (K.obj i)) (S : Sieve ((iteratedForward K).obj U)) :
    S ∈ topology J K ((iteratedForward K).obj U) ↔
      S.functorPullback (iteratedForward K) ∈
        CategoryTheory.Sigma.topology (fun i => (J.over X).over (K.obj i)) U := by
  rcases U with ⟨i, U⟩
  let e := (K.obj i).iteratedSliceEquiv
  let R : Sieve (e.functor.obj U) :=
    S.functorPullback (CategoryTheory.Sigma.incl i)
  change R ∈ (J.over (K.obj i).left) (e.functor.obj U) ↔
    R.functorPullback e.functor ∈ ((J.over X).over (K.obj i)) U
  constructor
  · intro hR
    exact e.functor.cover_lift ((J.over X).over (K.obj i)) (J.over (K.obj i).left) hR
  · intro hR
    have h := (e.functor.functorPushforward_mem_iff
      ((J.over X).over (K.obj i)) (J.over (K.obj i).left)).mpr hR
    rwa [(Sieve.essSurjFullFunctorGaloisInsertion e.functor U).l_u_eq R] at h

/-- The inverse image of a family morphism is restriction along its site map. -/
def mapPullback (J : GrothendieckTopology C) (f : K ⟶ L) :
    Sheaf (topology J L) (Type (max w u v)) ⥤ Sheaf (topology J K) (Type (max w u v)) :=
  (siteMap f).sheafPushforwardContinuous (Type (max w u v)) (topology J K) (topology J L)

/-- Restriction along the site map of a family morphism preserves finite limits. -/
instance mapPullback_preservesFiniteLimits (J : GrothendieckTopology C) (f : K ⟶ L) :
    PreservesFiniteLimits (mapPullback J f) := by
  let e := Functor.sheafPushforwardContinuousCompSheafToPresheafIso
    (siteMap f) (Type (max w u v)) (topology J K) (topology J L)
  letI : PreservesFiniteLimits
      (sheafToPresheaf (topology J L) (Type (max w u v)) ⋙
        (Functor.whiskeringLeft _ _ _).obj (siteMap f).op) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteLimits
      (mapPullback J f ⋙ sheafToPresheaf (topology J K) (Type (max w u v))) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves (mapPullback J f)
    (sheafToPresheaf (topology J K) (Type (max w u v)))

/-- Inverse image evaluates at the relocalized component selected by the family morphism. -/
theorem mapPullback_obj (J : GrothendieckTopology C) (f : K ⟶ L)
    (F : Sheaf (topology J L) (Type (max w u v))) (i : K.I)
    (U : CategoryTheory.Over (K.obj i).left) :
    ((mapPullback J f).obj F).obj.obj (op ⟨i, U⟩) =
      F.obj.obj (op ⟨f.f i, CategoryTheory.Over.mk (U.hom ≫ (f.φ i).left)⟩) := by
  rfl

/-- The bundled left-exact inverse-image functor of a family morphism. -/
def mapInverseImage (J : GrothendieckTopology C) (f : K ⟶ L) :
    Sheaf (topology J L) (Type (max w u v)) ⥤ₗ Sheaf (topology J K) (Type (max w u v)) :=
  LeftExactFunctor.of (mapPullback J f)

/-- Direct image of a family morphism is the right Kan extension along its opposite site map. -/
noncomputable def mapPushforward (J : GrothendieckTopology C) (f : K ⟶ L) :
    Sheaf (topology J K) (Type (max w u v)) ⥤ Sheaf (topology J L) (Type (max w u v)) :=
  (siteMap f).sheafPushforwardCocontinuous (Type (max w u v)) (topology J K) (topology J L)

/-- The left-exact inverse image of a family morphism is left adjoint to its direct image. -/
noncomputable def mapAdjunction (J : GrothendieckTopology C) (f : K ⟶ L) :
    (mapInverseImage J f).obj ⊣ mapPushforward J f :=
  (siteMap f).sheafAdjunctionCocontinuous (Type (max w u v)) (topology J K) (topology J L)

/-- Inverse and direct image have respectively the restriction and right-Kan-extension presheaves. -/
theorem map_spec (J : GrothendieckTopology C) (f : K ⟶ L)
    (F : Sheaf (topology J L) (Type (max w u v)))
    (G : Sheaf (topology J K) (Type (max w u v))) :
    ((mapInverseImage J f).obj.obj F).obj = (siteMap f).op ⋙ F.obj ∧
      ((mapPushforward J f).obj G).obj = (siteMap f).op.ran.obj G.obj := by
  constructor <;> rfl

end CategoryTheory.Limits.FormalCoproduct.Over
