module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.Topology.Sheaves.InverseLimit.PullbackSections
public import ReasLib.Topology.Sheaves.Pushforward.SectionFamilies

/-!
# Compatible sheaf systems over inverse limits of spaces

This module packages sheaves on the stages of an inverse system of spaces together with their
compatible transition maps.  It constructs the induced diagram on the limit space and the
canonical comparison maps on sections over inverse images of opens.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TopCat.Sheaf
open TopCat.Presheaf.Pushforward renaming id → pushforwardId

noncomputable section

universe u v w

namespace TopCat.Sheaf.InverseLimit

variable {C : Type (w + 1)} [Category.{w} C]
variable {I : Type u} [Category.{v} I] {F : I ⥤ TopCat.{w}}

/-- A compatible inverse system of `C`-valued sheaves on a diagram of spaces.  For
`a : j ⟶ i`, `stageMap a` is a morphism `𝓕ᵢ ⟶ (F.map a)∗ 𝓕ⱼ`. -/
structure SheafSystem (F : I ⥤ TopCat.{w}) where
  /-- The sheaf on the stage indexed by `i`. -/
  stageSheaf : ∀ i : I, (F.obj i).Sheaf C
  /-- The pushforward-form transition morphism associated to `a : j ⟶ i`. -/
  stageMap : ∀ {j i : I} (a : j ⟶ i),
    stageSheaf i ⟶ (pushforward C (F.map a)).obj (stageSheaf j)
  /-- The transition attached to an identity arrow is the canonical identity comparison. -/
  stageMap_id : ∀ i : I,
    stageMap (𝟙 i) =
      ⟨(pushforwardId (stageSheaf i).presheaf).inv ≫
        (TopCat.Presheaf.pushforwardEq (F.map_id i) (stageSheaf i).presheaf).inv⟩
  /-- Transition morphisms respect composition in the inverse system. -/
  stageMap_comp : ∀ {i j k : I} (a : j ⟶ i) (b : k ⟶ j),
    stageMap (b ≫ a) =
      ⟨(stageMap a ≫ (pushforward C (F.map a)).map (stageMap b)).1 ≫
        (TopCat.Presheaf.pushforwardEq (F.map_comp b a) (stageSheaf k).presheaf).inv⟩

namespace SheafSystem

/-- Construct a compatible sheaf system from its stage sheaves, transitions, and laws. -/
def of (stageSheaf : ∀ i : I, (F.obj i).Sheaf C)
    (stageMap : ∀ {j i : I} (a : j ⟶ i),
      stageSheaf i ⟶ (pushforward C (F.map a)).obj (stageSheaf j))
    (stageMap_id : ∀ i : I,
      stageMap (𝟙 i) =
        ⟨(pushforwardId (stageSheaf i).presheaf).inv ≫
          (TopCat.Presheaf.pushforwardEq (F.map_id i) (stageSheaf i).presheaf).inv⟩)
    (stageMap_comp : ∀ {i j k : I} (a : j ⟶ i) (b : k ⟶ j),
      stageMap (b ≫ a) =
        ⟨(stageMap a ≫ (pushforward C (F.map a)).map (stageMap b)).1 ≫
          (TopCat.Presheaf.pushforwardEq (F.map_comp b a) (stageSheaf k).presheaf).inv⟩) :
    SheafSystem (C := C) F :=
  { stageSheaf := stageSheaf
    stageMap := stageMap
    stageMap_id := stageMap_id
    stageMap_comp := stageMap_comp }

/-- The identity and composition laws defining a compatible sheaf system. -/
theorem stageMap_spec (system : SheafSystem (C := C) F) :
    (∀ i : I,
      system.stageMap (𝟙 i) =
        ⟨(pushforwardId (system.stageSheaf i).presheaf).inv ≫
          (TopCat.Presheaf.pushforwardEq
            (F.map_id i) (system.stageSheaf i).presheaf).inv⟩) ∧
    (∀ {i j k : I} (a : j ⟶ i) (b : k ⟶ j),
      system.stageMap (b ≫ a) =
        ⟨(system.stageMap a ≫
            (pushforward C (F.map a)).map (system.stageMap b)).1 ≫
          (TopCat.Presheaf.pushforwardEq
            (F.map_comp b a) (system.stageSheaf k).presheaf).inv⟩) := sorry

/-- A morphism in the over category determines the corresponding factorization of projection
maps in the inverse system of spaces. -/
theorem projectionPushforwardMap_eq {i : I} {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    F.map B.unop.hom = F.map u.unop.left ≫ F.map A.unop.hom := sorry

/-- The morphism between pushforwards of stage sheaves induced by an arrow in the over category.
For `u : A ⟶ B` in `(Over i)ᵒᵖ`, it maps the pushforward of the sheaf at `A` along
`F.map A.unop.hom` to the corresponding pushforward at `B`. -/
noncomputable def projectionPushforwardMap (system : SheafSystem (C := C) F)
    {i : I} {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    (pushforward C (F.map A.unop.hom)).obj (system.stageSheaf A.unop.left) ⟶
      (pushforward C (F.map B.unop.hom)).obj (system.stageSheaf B.unop.left) :=
  ⟨((pushforward C (F.map A.unop.hom)).map (system.stageMap u.unop.left)).1 ≫
    (TopCat.Presheaf.pushforwardEq
      (projectionPushforwardMap_eq u)
      (system.stageSheaf B.unop.left).presheaf).inv⟩

/-- The over-category pushforward transition attached to an identity arrow is the identity. -/
theorem projectionPushforwardMap_id (system : SheafSystem (C := C) F)
    {i : I} (A : (Over i)ᵒᵖ) :
    system.projectionPushforwardMap (𝟙 A) = 𝟙 _ := sorry

/-- The over-category pushforward transitions respect composition. -/
theorem projectionPushforwardMap_comp (system : SheafSystem (C := C) F)
    {i : I} {A B D : (Over i)ᵒᵖ} (u : A ⟶ B) (v : B ⟶ D) :
    system.projectionPushforwardMap (u ≫ v) =
      system.projectionPushforwardMap u ≫ system.projectionPushforwardMap v := sorry

/-- The diagram on `F.obj i` whose value at `a : j ⟶ i` is
`(pushforward C (F.map a)).obj (system.stageSheaf j)`. -/
noncomputable def projectionPushforwardDiagram (system : SheafSystem (C := C) F)
    (i : I) :
    (Over i)ᵒᵖ ⥤ (F.obj i).Sheaf C where
  obj A :=
    (pushforward C (F.map A.unop.hom)).obj (system.stageSheaf A.unop.left)
  map u := system.projectionPushforwardMap u
  map_id A := system.projectionPushforwardMap_id A
  map_comp u v := system.projectionPushforwardMap_comp u v

/-- The object of `projectionPushforwardDiagram` at `a : j ⟶ i` is
`(pushforward C (F.map a)).obj (system.stageSheaf j)`. -/
@[simp]
theorem projectionPushforwardDiagram_obj (system : SheafSystem (C := C) F)
    (i : I) (A : (Over i)ᵒᵖ) :
    (system.projectionPushforwardDiagram i).obj A =
      (pushforward C (F.map A.unop.hom)).obj (system.stageSheaf A.unop.left) := sorry

/-- The morphism of `projectionPushforwardDiagram` is the canonical map induced by the
compatible transition in the sheaf system. -/
@[simp]
theorem projectionPushforwardDiagram_map (system : SheafSystem (C := C) F)
    {i : I} {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    (system.projectionPushforwardDiagram i).map u = system.projectionPushforwardMap u := sorry

section

variable {FC : C → C → Type w} {CC : C → Type w}
variable [∀ P Q, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{w} C FC]
variable [HasColimits C] [HasLimits C]
variable [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]

/-- The transition `F.map a`-map in pullback form
`(F.map a)⁻¹ 𝓕ᵢ ⟶ 𝓕ⱼ`. -/
noncomputable def stagePullbackMap (system : SheafSystem (C := C) F) {j i : I} (a : j ⟶ i) :
    ((F.map a)⁻¹).obj (system.stageSheaf i) ⟶ system.stageSheaf j :=
  ((pullbackPushforwardAdjunction C (F.map a)).homEquiv
    (system.stageSheaf i) (system.stageSheaf j)).symm (system.stageMap a)

end

/-- For `A = (a : j ⟶ i)` in `Over i`, the inverse image `fₐ⁻¹(U)` on `F.obj j`. -/
abbrev projectionOpen (i : I) (U : Opens (F.obj i)) (A : Over i) :
    Opens (F.obj A.left) :=
  (Opens.map (F.map A.hom)).obj U

/-- A morphism in `Over i` identifies the source projection open with the inverse image of the
target projection open. -/
theorem projectionOpen_le (i : I) (U : Opens (F.obj i))
    {A B : Over i} (φ : A ⟶ B) :
    projectionOpen i U A ≤
      (Opens.map (F.map φ.left)).obj (projectionOpen i U B) := sorry

/-- The restriction map on stagewise sections induced by a morphism in `Over i`. -/
noncomputable def projectionOpenSectionsMap (system : SheafSystem (C := C) F)
    (i : I) (U : Opens (F.obj i)) {A B : Over i} (φ : A ⟶ B) :
    (system.stageSheaf B.left).presheaf.obj (op (projectionOpen i U B)) ⟶
      (system.stageSheaf A.left).presheaf.obj (op (projectionOpen i U A)) :=
  (ContinuousMapSheafMapFamily.homEquiv (system.stageMap φ.left)).app
    (projectionOpen i U A) (projectionOpen i U B) (projectionOpen_le i U φ)

/-- Stagewise section transitions preserve identity arrows. -/
theorem projectionOpenSectionsMap_id (system : SheafSystem (C := C) F)
    (i : I) (U : Opens (F.obj i)) (A : Over i) :
    system.projectionOpenSectionsMap i U (𝟙 A) = 𝟙 _ := sorry

/-- Stagewise section transitions preserve composition contravariantly. -/
theorem projectionOpenSectionsMap_comp (system : SheafSystem (C := C) F)
    (i : I) (U : Opens (F.obj i)) {A B D : Over i}
    (φ : A ⟶ B) (ψ : B ⟶ D) :
    system.projectionOpenSectionsMap i U (φ ≫ ψ) =
      system.projectionOpenSectionsMap i U ψ ≫
        system.projectionOpenSectionsMap i U φ := sorry

/-- The diagram `(a : j ⟶ i) ↦ 𝓕ⱼ(fₐ⁻¹(U))` of stagewise sections. -/
noncomputable def projectionOpenSectionDiagram (system : SheafSystem (C := C) F)
    (i : I) (U : Opens (F.obj i)) :
    (Over i)ᵒᵖ ⥤ C where
  obj A :=
    (system.stageSheaf A.unop.left).presheaf.obj
      (op (projectionOpen i U A.unop))
  map φ := system.projectionOpenSectionsMap i U φ.unop
  map_id A := system.projectionOpenSectionsMap_id i U A.unop
  map_comp φ ψ := system.projectionOpenSectionsMap_comp i U ψ.unop φ.unop

section

variable {FC : C → C → Type w} {CC : C → Type w}
variable [∀ P Q, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{w} C FC]
variable [HasColimits C] [HasLimits C]
variable [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable [HasLimit F]

/-- The canonical transition between the pullbacks of stage sheaves to the limit space. -/
noncomputable def limitPullbackMap (system : SheafSystem (C := C) F) {A B : Iᵒᵖ} (a : A ⟶ B) :
    ((limit.π F A.unop)⁻¹).obj (system.stageSheaf A.unop) ⟶
      ((limit.π F B.unop)⁻¹).obj (system.stageSheaf B.unop) :=
  eqToHom
      (congrArg
        (fun q : limit F ⟶ F.obj A.unop ↦
          ((q⁻¹).obj (system.stageSheaf A.unop)))
        (limit.w F a.unop).symm) ≫
    (pullbackComp (A := C)
      (limit.π F B.unop) (F.map a.unop)).inv.app (system.stageSheaf A.unop) ≫
    ((limit.π F B.unop)⁻¹).map (system.stagePullbackMap a.unop)

/-- Pullback transitions on the limit space preserve identity arrows. -/
theorem limitPullbackMap_id (system : SheafSystem (C := C) F) (A : Iᵒᵖ) :
    system.limitPullbackMap (𝟙 A) = 𝟙 _ := sorry

/-- Pullback transitions on the limit space preserve composition. -/
theorem limitPullbackMap_comp (system : SheafSystem (C := C) F)
    {A B D : Iᵒᵖ} (a : A ⟶ B) (b : B ⟶ D) :
    system.limitPullbackMap (a ≫ b) =
      system.limitPullbackMap a ≫ system.limitPullbackMap b := sorry

/-- The canonical diagram `i ↦ pᵢ⁻¹ 𝓕ᵢ` of sheaves on the inverse-limit space. -/
noncomputable def limitPullbackDiagram (system : SheafSystem (C := C) F) :
    Iᵒᵖ ⥤ (limit F).Sheaf C where
  obj A := ((limit.π F A.unop)⁻¹).obj (system.stageSheaf A.unop)
  map a := system.limitPullbackMap a
  map_id A := system.limitPullbackMap_id A
  map_comp a b := system.limitPullbackMap_comp a b

/-- The canonical colimit sheaf `colimᵢ pᵢ⁻¹ 𝓕ᵢ` on the inverse-limit space. -/
noncomputable abbrev colimitSheaf (system : SheafSystem (C := C) F)
    [HasColimit system.limitPullbackDiagram] :
    (limit F).Sheaf C :=
  colimit system.limitPullbackDiagram

/-- The canonical map from the pushforward of a stage sheaf along its projection to the
pushforward of the colimit sheaf along the corresponding limit projection. -/
noncomputable def projectionPushforwardToColimitMap (system : SheafSystem (C := C) F)
    [HasColimit system.limitPullbackDiagram]
    (i : I) (A : (Over i)ᵒᵖ) :
    (pushforward C (F.map A.unop.hom)).obj (system.stageSheaf A.unop.left) ⟶
      (pushforward C (limit.π F i)).obj system.colimitSheaf :=
  (pushforward C (F.map A.unop.hom)).map
      ((pullbackPushforwardAdjunction C (limit.π F A.unop.left)).unit.app
        (system.stageSheaf A.unop.left)) ≫
    eqToHom
      (congrArg
        (fun f ↦ (pushforward C f).obj
          (system.limitPullbackDiagram.obj (op A.unop.left)))
        (limit.w F A.unop.hom)) ≫
    (pushforward C (limit.π F i)).map
      (colimit.ι system.limitPullbackDiagram (op A.unop.left))

/-- The maps from pushforwarded stage sheaves to the pushforward of the colimit sheaf are
compatible with morphisms in the over category. -/
theorem projectionPushforwardToColimitMap_naturality (system : SheafSystem (C := C) F)
    [HasColimit system.limitPullbackDiagram]
    (i : I) {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    system.projectionPushforwardMap u ≫ system.projectionPushforwardToColimitMap i B =
      system.projectionPushforwardToColimitMap i A ≫
        ((Functor.const (Over i)ᵒᵖ).obj
          ((pushforward C (limit.π F i)).obj system.colimitSheaf)).map u := sorry

/-- The cocone from the pushforwarded stage-sheaf diagram on `F.obj i` to the pushforward of
the canonical colimit sheaf along the limit projection `pᵢ`. -/
noncomputable def projectionPushforwardToColimitCocone (system : SheafSystem (C := C) F)
    [HasColimit system.limitPullbackDiagram]
    (i : I) :
    Cocone (system.projectionPushforwardDiagram i) where
  pt := (pushforward C (limit.π F i)).obj system.colimitSheaf
  ι :=
    { app := fun A ↦ system.projectionPushforwardToColimitMap i A
      naturality := fun {_ _} u ↦
        system.projectionPushforwardToColimitMap_naturality i u }

/-- The universal comparison from the colimit of the pushforwarded stage-sheaf diagram on
`F.obj i` to the pushforward of the canonical colimit sheaf along `pᵢ`. -/
noncomputable def projectionPushforwardToColimitComparison (system : SheafSystem (C := C) F)
    [HasColimit system.limitPullbackDiagram]
    (i : I) [HasColimit (system.projectionPushforwardDiagram i)] :
    colimit (system.projectionPushforwardDiagram i) ⟶
      (pushforward C (limit.π F i)).obj system.colimitSheaf :=
  colimit.desc (system.projectionPushforwardDiagram i)
    (system.projectionPushforwardToColimitCocone i)

/-- The inverse image `pᵢ⁻¹(U)` on the inverse-limit space. -/
abbrev limitProjectionOpen (i : I) (U : Opens (F.obj i)) :
    Opens (limit F : TopCat.{w}) :=
  (Opens.map (limit.π F i)).obj U

/-- The inverse image `pᵢ⁻¹(U)` is contained in the pullback along `pⱼ` of
`fₐ⁻¹(U)` for every `A = (a : j ⟶ i)`. -/
theorem limitProjectionOpen_le (i : I) (U : Opens (F.obj i)) (A : Over i) :
    limitProjectionOpen i U ≤
      (Opens.map (limit.π F A.left)).obj (projectionOpen i U A) := sorry

/-- A section of `𝓕ⱼ` on `fₐ⁻¹(U)` maps canonically to a section of
`pⱼ⁻¹ 𝓕ⱼ` on `pᵢ⁻¹(U)`. -/
noncomputable def projectionOpenSectionsToPullbackMap (system : SheafSystem (C := C) F)
    (i : I) (U : Opens (F.obj i)) (A : Over i) :
    (system.stageSheaf A.left).presheaf.obj (op (projectionOpen i U A)) ⟶
      (((limit.π F A.left)⁻¹).obj (system.stageSheaf A.left)).presheaf.obj
        (op (limitProjectionOpen i U)) :=
  (ContinuousMapSheafMapFamily.homEquiv
    ((pullbackPushforwardAdjunction C (limit.π F A.left)).unit.app
      (system.stageSheaf A.left))).app
        (limitProjectionOpen i U) (projectionOpen i U A)
        (limitProjectionOpen_le i U A)

/-- The cocone leg from stagewise sections to sections of the colimit sheaf on `pᵢ⁻¹(U)`. -/
noncomputable def projectionOpenSectionsToColimitMap (system : SheafSystem (C := C) F)
    [HasColimit system.limitPullbackDiagram]
    (i : I) (U : Opens (F.obj i)) (A : Over i) :
    (system.stageSheaf A.left).presheaf.obj (op (projectionOpen i U A)) ⟶
      system.colimitSheaf.presheaf.obj (op (limitProjectionOpen i U)) :=
  system.projectionOpenSectionsToPullbackMap i U A ≫
    (colimit.ι system.limitPullbackDiagram (op A.left)).1.app
      (op (limitProjectionOpen i U))

/-- The maps from stagewise sections to the colimit sheaf are compatible with morphisms in
`Over i`. -/
theorem projectionOpenSectionsToColimitMap_naturality (system : SheafSystem (C := C) F)
    [HasColimit system.limitPullbackDiagram]
    (i : I) (U : Opens (F.obj i)) {A B : Over i} (φ : A ⟶ B) :
    system.projectionOpenSectionsMap i U φ ≫
        system.projectionOpenSectionsToColimitMap i U A =
      system.projectionOpenSectionsToColimitMap i U B := sorry

/-- The legs from stagewise sections to colimit sections satisfy cocone naturality. -/
theorem projectionOpenSectionsCocone_naturality (system : SheafSystem (C := C) F)
    [HasColimit system.limitPullbackDiagram]
    (i : I) (U : Opens (F.obj i)) {A B : (Over i)ᵒᵖ} (φ : A ⟶ B) :
    (system.projectionOpenSectionDiagram i U).map φ ≫
        system.projectionOpenSectionsToColimitMap i U B.unop =
      system.projectionOpenSectionsToColimitMap i U A.unop ≫
        ((Functor.const (Over i)ᵒᵖ).obj
          (system.colimitSheaf.presheaf.obj
            (op (limitProjectionOpen i U)))).map φ := sorry

/-- The canonical cocone from `(a : j ⟶ i) ↦ 𝓕ⱼ(fₐ⁻¹(U))` to sections of the colimit sheaf on
`pᵢ⁻¹(U)`. -/
noncomputable def projectionOpenSectionsCocone (system : SheafSystem (C := C) F)
    [HasColimit system.limitPullbackDiagram]
    (i : I) (U : Opens (F.obj i)) :
    Cocone (system.projectionOpenSectionDiagram i U) where
  pt := system.colimitSheaf.presheaf.obj (op (limitProjectionOpen i U))
  ι :=
    { app := fun A ↦ system.projectionOpenSectionsToColimitMap i U A.unop
      naturality := fun {_ _} φ ↦
        system.projectionOpenSectionsCocone_naturality i U φ }

/-- The canonical comparison from stagewise sections to sections of the colimit sheaf. -/
noncomputable def projectionOpenSectionsComparison (system : SheafSystem (C := C) F)
    [HasColimit system.limitPullbackDiagram]
    (i : I) (U : Opens (F.obj i))
    [HasColimit (system.projectionOpenSectionDiagram i U)] :
    colimit (system.projectionOpenSectionDiagram i U) ⟶
      system.colimitSheaf.presheaf.obj (op (limitProjectionOpen i U)) :=
  colimit.desc (system.projectionOpenSectionDiagram i U)
    (system.projectionOpenSectionsCocone i U)

/-- For a cofiltered diagram of spectral spaces with spectral transition maps, the canonical
comparison from stagewise sections over a compact open to sections of the colimit sheaf is an
isomorphism. -/
theorem projectionOpenSectionsComparison_isIso (system : SheafSystem (C := C) F)
    [IsCofiltered I] [∀ j : I, SpectralSpace (F.obj j)]
    (hF : ∀ {j i : I} (a : j ⟶ i), IsSpectralMap (F.map a))
    [HasColimit system.limitPullbackDiagram]
    (i : I) (U : CompactOpens (F.obj i))
    [HasColimit (system.projectionOpenSectionDiagram i U.toOpens)] :
    IsIso (system.projectionOpenSectionsComparison i U.toOpens) := sorry

end

end SheafSystem

end TopCat.Sheaf.InverseLimit
