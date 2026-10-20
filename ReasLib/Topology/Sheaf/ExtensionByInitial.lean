module

public import ReasLib.Topology.Sheaf.ExtensionByInitial.Basic
public import ReasLib.Topology.Sheaf.Pushforward
public import ReasLib.Topology.Presheaf.ExtensionByInitial.Properties
public import ReasLib.Topology.Sheaves.Pullback.Forget
public import ReasLib.Topology.Sheaves.Stalks.Pullback
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Properties of extension by an initial object

This module is the canonical sheaf-level API for extension by an initial object along an open
subspace inclusion. The construction itself is owned by
`TopCat.Presheaf.ExtensionByInitial` and `TopCat.Sheaf.ExtensionByInitial`; the generic
presheaf adjunction lives in `TopCat.Presheaf.ExtensionByInitial.Properties`. This file owns the
sheaf adjunction, stalk, essential-image, and coefficient-category-specialized properties.

The sheaf API is organized under the construction namespaces:

- `TopCat.Sheaf.ExtensionByInitial.Properties` for the sheaf adjunction and stalks;
- `TopCat.Sheaf.ExtensionByInitial.Type` and `.AddCommGrp` for common coefficients.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits
open TopCat.Opens.Subspace

noncomputable section

universe w v u

section Sheaf

variable {X : TopCat.{w}}
variable {C : Type u} [Category.{w} C] [HasInitial C] [HasColimits C]
variable [HasLimits C]
variable {FC : C → C → Type w} {CC : C → Type w}
variable [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory.{w} C FC]
variable [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable [HasWeakSheafify (Opens.grothendieckTopology X) C]

namespace TopCat.Sheaf.ExtensionByInitial.Properties

/-- The Hom equivalence characterizing sheaf extension by an initial object. -/
noncomputable def homEquiv (U : Opens X) (ℱ : (space U).Sheaf C)
    (𝒢 : X.Sheaf C) :
    ((TopCat.Sheaf.ExtensionByInitial.functor U).obj ℱ ⟶ 𝒢) ≃
      (ℱ ⟶ (TopCat.Sheaf.pullback C (inclusion U)).obj 𝒢) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) C).homEquiv
      ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ.presheaf) 𝒢).trans
    ((TopCat.Presheaf.ExtensionByInitial.Properties.homEquiv
        U ℱ.presheaf 𝒢.presheaf).trans
      ((Iso.homCongr (Iso.refl _)
          ((U.isOpenEmbedding.pullbackForgetIso (C := C)).app 𝒢)).trans
        ((fullyFaithfulSheafToPresheaf
          (Opens.grothendieckTopology (space U)) C).homEquiv).symm))

/-- The inverse transpose of a morphism into sheaf pullback. -/
noncomputable def lift (U : Opens X) {ℱ : (space U).Sheaf C} {𝒢 : X.Sheaf C}
    (η : ℱ ⟶ (TopCat.Sheaf.pullback C (inclusion U)).obj 𝒢) :
    (TopCat.Sheaf.ExtensionByInitial.functor U).obj ℱ ⟶ 𝒢 :=
  (homEquiv U ℱ 𝒢).symm η

/-- The inverse Hom transpose is natural in its source sheaf. -/
theorem homEquiv_naturality_left_symm (U : Opens X)
    {ℱ' ℱ : (space U).Sheaf C} {𝒢 : X.Sheaf C}
    (f : ℱ' ⟶ ℱ)
    (g : ℱ ⟶ (TopCat.Sheaf.pullback C (inclusion U)).obj 𝒢) :
    (homEquiv U ℱ' 𝒢).symm (f ≫ g) =
      (TopCat.Sheaf.ExtensionByInitial.functor U).map f ≫
        (homEquiv U ℱ 𝒢).symm g := sorry

/-- The forward Hom transpose is natural in its target sheaf. -/
theorem homEquiv_naturality_right (U : Opens X)
    {ℱ : (space U).Sheaf C} {𝒢 𝒢' : X.Sheaf C}
    (f : (TopCat.Sheaf.ExtensionByInitial.functor U).obj ℱ ⟶ 𝒢)
    (g : 𝒢 ⟶ 𝒢') :
    homEquiv U ℱ 𝒢' (f ≫ g) =
      homEquiv U ℱ 𝒢 f ≫
        (TopCat.Sheaf.pullback C (inclusion U)).map g := sorry

/-- The adjunction from sheaf extension by an initial object to sheaf pullback. -/
noncomputable def adjunction (U : Opens X) :
    TopCat.Sheaf.ExtensionByInitial.functor U ⊣
      (TopCat.Sheaf.pullback C (inclusion U) : X.Sheaf C ⥤ (space U).Sheaf C) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv U
      homEquiv_naturality_left_symm := homEquiv_naturality_left_symm U
      homEquiv_naturality_right := homEquiv_naturality_right U }

/-- The Hom equivalence of the canonical adjunction is the explicit sheaf Hom equivalence. -/
theorem adjunction_homEquiv (U : Opens X) (ℱ : (space U).Sheaf C)
    (𝒢 : X.Sheaf C) :
    (adjunction (C := C) U).homEquiv ℱ 𝒢 = homEquiv U ℱ 𝒢 := sorry

/-- The counit component is the inverse transpose of the identity on the pulled-back sheaf. -/
theorem adjunction_counit_app (U : Opens X) (𝒢 : X.Sheaf C) :
    (adjunction (C := C) U).counit.app 𝒢 =
      lift U (𝟙 ((TopCat.Sheaf.pullback C (inclusion U)).obj 𝒢)) := sorry

/-- At a point of the open subspace, the unit of any such adjunction induces a stalk
isomorphism. -/
theorem stalkIso_of_mem_of_adj (U : Opens X) (ℱ : (space U).Sheaf C)
    (adj : TopCat.Sheaf.ExtensionByInitial.functor U ⊣
      TopCat.Sheaf.pullback C (inclusion U)) (x : space U) :
    IsIso
      ((TopCat.Presheaf.stalkFunctor C x).map
          ((TopCat.Sheaf.forget C (space U)).map (adj.unit.app ℱ)) ≫
        (TopCat.Sheaf.stalkPullbackIso (inclusion U)
          ((TopCat.Sheaf.ExtensionByInitial.functor U).obj ℱ) x).inv) := sorry

/-- At a point of the open subspace, the canonical unit induces a stalk isomorphism. -/
theorem stalkIso_of_mem (U : Opens X) (ℱ : (space U).Sheaf C) (x : space U) :
    IsIso
      ((TopCat.Presheaf.stalkFunctor C x).map
          ((TopCat.Sheaf.forget C (space U)).map
            ((adjunction (C := C) U).unit.app ℱ)) ≫
        (TopCat.Sheaf.stalkPullbackIso (inclusion U)
          ((TopCat.Sheaf.ExtensionByInitial.functor U).obj ℱ) x).inv) := sorry

/-- Outside the open subspace, the stalk of extension by an initial object is initial. -/
theorem stalk_isInitial_of_not_mem (U : Opens X) (ℱ : (space U).Sheaf C)
    (x : X) (hx : x ∉ (U : Set X)) :
    IsIso (initial.to
      (((TopCat.Sheaf.ExtensionByInitial.functor U).obj ℱ).presheaf.stalk x)) := sorry

/-- Restricting the presheaf extension `jₚ! ℱ` along the open-subspace inclusion recovers `ℱ`:
the inverse of the presheaf unit, transported along the open-map description of pullback. -/
noncomputable def presheafRestrictIso (U : Opens X) (ℱ : (space U).Presheaf C) :
    U.isOpenEmbedding.functor.op ⋙ (TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ ≅
      ℱ :=
  (U.isOpenEmbedding.isOpenMap.pullbackObjIso
      ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ)).symm ≪≫
    (TopCat.Presheaf.ExtensionByInitial.Properties.unitIso U ℱ).symm

/-- The explicit inverse of the sheaf unit, `j⁻¹ j! ℱ ≅ ℱ`: sheaf pullback along the open
inclusion is restriction along the image functor, restriction commutes with sheafification
(the image functor of an open embedding is continuous and cocontinuous), restriction of
`jₚ! ℱ` recovers `ℱ`, and the sheafification of a sheaf is the sheaf itself. -/
noncomputable def pullbackObjIso (U : Opens X) (ℱ : (space U).Sheaf C) :
    (TopCat.Sheaf.pullback C (inclusion U)).obj
        ((TopCat.Sheaf.ExtensionByInitial.functor U).obj ℱ) ≅ ℱ :=
  -- Local instance justification (defeq pin): use the continuity witness for the exact
  -- image-open functor occurring in mathlib's `sheafPullback` construction.
  haveI := U.isOpenEmbedding.functor_isContinuous
  -- Local instance justification (defeq pin): use the same image-open functor in the
  -- sheafification comparison, with cocontinuity supplied by its open-map adjunction.
  haveI : U.isOpenEmbedding.functor.IsCocontinuous
      (Opens.grothendieckTopology (space U)) (Opens.grothendieckTopology X) :=
    (U.isOpenEmbedding.isOpenMap.adjunction.isCocontinuous_iff_coverPreserving _ _).mpr
      (coverPreserving_opens_map (inclusion U))
  (U.isOpenEmbedding.sheafPullbackIso C).app _ ≪≫
    ((U.isOpenEmbedding.functor.pushforwardContinuousSheafificationCompatibility C
        (Opens.grothendieckTopology (space U)) (Opens.grothendieckTopology X)).app
      ((TopCat.Presheaf.ExtensionByInitial.functor U).obj ℱ.presheaf)).symm ≪≫
    (presheafToSheaf _ C).mapIso (presheafRestrictIso U ℱ.presheaf) ≪≫
    (sheafificationIso ℱ).symm

/-- The canonical unit followed by the explicit inverse is the identity. -/
theorem unit_app_comp_pullbackObjIso_hom (U : Opens X) (ℱ : (space U).Sheaf C) :
    (adjunction (C := C) U).unit.app ℱ ≫ (pullbackObjIso U ℱ).hom = 𝟙 ℱ := sorry

/-- The explicit inverse followed by the canonical unit is the identity. -/
theorem pullbackObjIso_hom_comp_unit_app (U : Opens X) (ℱ : (space U).Sheaf C) :
    (pullbackObjIso U ℱ).hom ≫ (adjunction (C := C) U).unit.app ℱ = 𝟙 _ := sorry

/-- The unit component `ℱ ≅ j⁻¹ j! ℱ` of the sheaf adjunction, with explicit inverse. -/
noncomputable def unitIso (U : Opens X) (ℱ : (space U).Sheaf C) :
    ℱ ≅ (TopCat.Sheaf.pullback C (inclusion U)).obj
      ((TopCat.Sheaf.ExtensionByInitial.functor U).obj ℱ) where
  hom := (adjunction (C := C) U).unit.app ℱ
  inv := (pullbackObjIso U ℱ).hom
  hom_inv_id := unit_app_comp_pullbackObjIso_hom U ℱ
  inv_hom_id := pullbackObjIso_hom_comp_unit_app U ℱ

/-- The unit of the canonical sheaf extension-by-initial adjunction is an isomorphism. -/
instance unit_isIso (U : Opens X) :
    IsIso (adjunction (C := C) U).unit :=
  have (ℱ : (space U).Sheaf C) : IsIso ((adjunction (C := C) U).unit.app ℱ) :=
    (unitIso U ℱ).isIso_hom
  NatIso.isIso_of_isIso_app _

/-- Sheaf extension by an initial object is fully faithful; a morphism `j! ℱ ⟶ j! 𝒢` is
transposed along the adjunction and composed with the explicit inverse unit. -/
noncomputable def fullyFaithful (U : Opens X) :
    (TopCat.Sheaf.ExtensionByInitial.functor (C := C) U).FullyFaithful where
  preimage {_ 𝒢} f := homEquiv U _ _ f ≫ (pullbackObjIso U 𝒢).hom
  map_preimage := sorry
  preimage_map := sorry

/-- The preimage of a morphism is its adjoint transpose followed by the explicit inverse unit. -/
@[simp] theorem fullyFaithful_preimage (U : Opens X) {ℱ 𝒢 : (space U).Sheaf C}
    (f : (TopCat.Sheaf.ExtensionByInitial.functor U).obj ℱ ⟶
      (TopCat.Sheaf.ExtensionByInitial.functor U).obj 𝒢) :
    (fullyFaithful U).preimage f = homEquiv U ℱ _ f ≫ (pullbackObjIso U 𝒢).hom := rfl

/-- A sheaf is in the essential image of extension by an initial object exactly when every stalk
outside the open subspace is initial. -/
theorem essImage_iff (U : Opens X) (𝒢 : X.Sheaf C) :
    (TopCat.Sheaf.ExtensionByInitial.functor U).essImage 𝒢 ↔
      ∀ x : X, x ∉ (U : Set X) → IsIso (initial.to (𝒢.presheaf.stalk x)) := sorry

end TopCat.Sheaf.ExtensionByInitial.Properties

namespace TopCat.Sheaf.ExtensionByInitial.Type

variable {X : TopCat.{w}}

/-- A `Type`-valued sheaf lies in the essential image exactly when its stalks outside the open
subspace are empty. -/
theorem essImage_iff (U : Opens X) (𝒢 : X.Sheaf (Type w)) :
    (TopCat.Sheaf.ExtensionByInitial.functor U).essImage 𝒢 ↔
      ∀ x : X, x ∉ (U : Set X) → IsEmpty (𝒢.presheaf.stalk x) := sorry

/-- Extension by the empty type from a proper open subspace does not preserve terminal
objects. -/
theorem not_preservesTerminal_of_ne_top (U : Opens X) (hU : U ≠ ⊤) :
    ¬ PreservesLimit (Functor.empty.{0} ((space U).Sheaf (Type w)))
      (TopCat.Sheaf.ExtensionByInitial.functor U :
        (space U).Sheaf (Type w) ⥤ X.Sheaf (Type w)) := sorry

/-- Extension by the empty type from a proper open subspace is not left exact. -/
theorem not_leftExact_of_ne_top (U : Opens X) (hU : U ≠ ⊤) :
    ¬ leftExactFunctor ((space U).Sheaf (Type w)) (X.Sheaf (Type w))
      (TopCat.Sheaf.ExtensionByInitial.functor U :
        (space U).Sheaf (Type w) ⥤ X.Sheaf (Type w)) := sorry

end TopCat.Sheaf.ExtensionByInitial.Type

namespace TopCat.Sheaf.ExtensionByInitial.AddCommGrp

variable {X : TopCat.{w}}

/-- An `AddCommGrp`-valued sheaf lies in the essential image exactly when its stalks outside the
open subspace are zero. -/
theorem essImage_iff (U : Opens X) (𝒢 : X.Sheaf AddCommGrpCat.{w}) :
    (TopCat.Sheaf.ExtensionByInitial.functor U).essImage 𝒢 ↔
      ∀ x : X, x ∉ (U : Set X) → IsZero (𝒢.presheaf.stalk x) := sorry

/-- Extension by zero for additive sheaves is exact. -/
theorem exact (U : Opens X) :
    exactFunctor ((space U).Sheaf AddCommGrpCat.{w}) (X.Sheaf AddCommGrpCat.{w})
      (TopCat.Sheaf.ExtensionByInitial.functor U :
        (space U).Sheaf AddCommGrpCat.{w} ⥤ X.Sheaf AddCommGrpCat.{w}) := sorry

end TopCat.Sheaf.ExtensionByInitial.AddCommGrp

end Sheaf

namespace TopCat.Sheaf.ExtensionByInitial.OpenEmbedding

variable {X U : TopCat.{w}} {j : U ⟶ X}

section Construction

variable {C : Type u} [Category.{v} C] [HasInitial C]
variable [HasWeakSheafify (Opens.grothendieckTopology X) C]

/-- The lower-shriek functor along an open embedding: transport to its image and then extend by
the initial object from that open subspace. -/
@[stacks 01AK "open-immersion lower-shriek functor"]
noncomputable def functor (hj : Topology.IsOpenEmbedding j) :
    U.Sheaf C ⥤ X.Sheaf C :=
  TopCat.Sheaf.pushforward C (TopCat.isoOfHomeo hj.1.toHomeomorph).hom ⋙
    TopCat.Sheaf.ExtensionByInitial.functor ⟨Set.range j, hj.isOpen_range⟩

/-- The open-embedding lower-shriek functor is transport to the image followed by the canonical
open-subspace extension functor. -/
theorem functor_def (hj : Topology.IsOpenEmbedding j) :
    functor (C := C) hj =
      TopCat.Sheaf.pushforward C (TopCat.isoOfHomeo hj.1.toHomeomorph).hom ⋙
        TopCat.Sheaf.ExtensionByInitial.functor ⟨Set.range j, hj.isOpen_range⟩ := sorry

end Construction

section Properties

variable {C : Type u} [Category.{w} C] [HasInitial C] [HasColimits C] [HasLimits C]
variable {FC : C → C → Type w} {CC : C → Type w}
variable [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory.{w} C FC]
variable [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable [HasWeakSheafify (Opens.grothendieckTopology X) C]

/-- Naive pullback along an open embedding factors through its open image and inverse
transport along the homeomorphism onto that image. -/
theorem sheafPullback_factorization (hj : Topology.IsOpenEmbedding j) :
    hj.sheafPullback C =
      (⟨Set.range j, hj.isOpen_range⟩ : Opens X).isOpenEmbedding.sheafPullback C ⋙
        TopCat.Sheaf.pushforward C (TopCat.isoOfHomeo hj.1.toHomeomorph).inv := sorry

/-- Pullback through the open image and inverse transport is naturally isomorphic to pullback
along the open embedding. -/
noncomputable def pullbackFactorizationIso (hj : Topology.IsOpenEmbedding j) :
    TopCat.Sheaf.pullback C (inclusion (⟨Set.range j, hj.isOpen_range⟩ : Opens X)) ⋙
        TopCat.Sheaf.pushforward C (TopCat.isoOfHomeo hj.1.toHomeomorph).inv ≅
      TopCat.Sheaf.pullback C j :=
  let V : Opens X := ⟨Set.range j, hj.isOpen_range⟩
  let e : U ≅ space V := TopCat.isoOfHomeo hj.1.toHomeomorph
  Functor.isoWhiskerRight (V.isOpenEmbedding.sheafPullbackIso C)
      (TopCat.Sheaf.pushforward C e.inv) ≪≫
    (eqToIso (sheafPullback_factorization (C := C) hj)).symm ≪≫
    (hj.sheafPullbackIso C).symm

/-- Extension by an initial object along an open embedding is left adjoint to sheaf pullback. -/
noncomputable def adjunction (hj : Topology.IsOpenEmbedding j) :
    functor (C := C) hj ⊣ TopCat.Sheaf.pullback C j :=
  let V : Opens X := ⟨Set.range j, hj.isOpen_range⟩
  let e : U ≅ space V := TopCat.isoOfHomeo hj.1.toHomeomorph
  ((TopCat.Sheaf.pushforwardEquivalence (C := C) e.hom).toAdjunction.comp
    (TopCat.Sheaf.ExtensionByInitial.Properties.adjunction (C := C) V)).ofNatIsoRight
      (Functor.isoWhiskerLeft (TopCat.Sheaf.pullback C (inclusion V))
          (eqToIso (congrArg (TopCat.Sheaf.pushforward C) (IsIso.Iso.inv_hom e))) ≪≫
        pullbackFactorizationIso (C := C) hj)

/-- The unit of extension by an initial object induces the comparison from a sheaf stalk to
its extended stalk at the image point. -/
noncomputable def stalkComparison (hj : Topology.IsOpenEmbedding j) (F : U.Sheaf C) (x : U) :
    F.presheaf.stalk x ⟶ ((functor (C := C) hj).obj F).presheaf.stalk (j x) :=
  (TopCat.Presheaf.stalkFunctor C x).map
      ((TopCat.Sheaf.forget C U).map ((adjunction (C := C) hj).unit.app F)) ≫
    (TopCat.Sheaf.stalkPullbackIso j ((functor (C := C) hj).obj F) x).inv

/-- The unit-induced stalk comparison for extension along an open embedding is invertible. -/
instance stalkComparison_isIso (hj : Topology.IsOpenEmbedding j) (F : U.Sheaf C) (x : U) :
    IsIso (stalkComparison hj F x) := sorry

end Properties

/-- Extension by the empty set along an open embedding has empty stalks outside its range. -/
theorem stalk_isEmpty_of_not_mem_range
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type w)]
    (hj : Topology.IsOpenEmbedding j) (F : U.Sheaf (Type w)) (x : X)
    (hx : x ∉ Set.range j) :
    IsEmpty (((functor (C := Type w) hj).obj F).presheaf.stalk x) := sorry

/-- Extension by zero along an open embedding has zero stalks outside its range. -/
theorem stalk_isZero_of_not_mem_range
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
    (hj : Topology.IsOpenEmbedding j) (F : U.Sheaf AddCommGrpCat.{w}) (x : X)
    (hx : x ∉ Set.range j) :
    IsZero (((functor (C := AddCommGrpCat.{w}) hj).obj F).presheaf.stalk x) := sorry

/-- Lower shriek along an open embedding is exact on sheaves of abelian groups. -/
@[stacks 01AK "open-immersion lower-shriek exactness"]
theorem exact
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
    (hj : Topology.IsOpenEmbedding j) :
    exactFunctor (U.Sheaf AddCommGrpCat.{w}) (X.Sheaf AddCommGrpCat.{w})
      (functor (C := AddCommGrpCat.{w}) hj) := sorry

end TopCat.Sheaf.ExtensionByInitial.OpenEmbedding

end

end
