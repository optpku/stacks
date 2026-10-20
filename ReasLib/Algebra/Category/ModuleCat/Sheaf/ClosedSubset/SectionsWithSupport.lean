module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ClosedSubset
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Sections.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Support

/-!
# Module sections supported on a closed subset

For a sheaf of rings `𝒪` on a topological space and a bundled closed subset `Z`, this file
constructs the kernel of restriction to `Z.compl`, restricts it to `Z`, and records its adjunction
with direct image from the closed subspace.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules.ClosedSubset.SectionsWithSupport

variable {X : TopCat.{u}} (𝒪 : X.Sheaf RingCat.{u}) (Z : Closeds X)

/-- The open complement of a bundled closed subset. -/
abbrev openComplement (Z : Closeds X) : Opens X :=
  Z.compl

/-- The structure-map unit attached to restriction to the open complement. -/
abbrev openComplementStructureMap :
    𝒪 ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} (openComplement Z).inclusion').obj
        ((TopCat.Sheaf.pullback RingCat.{u} (openComplement Z).inclusion').obj 𝒪) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
    (openComplement Z).inclusion').unit.app 𝒪

/-- Restriction of module sheaves to the open complement. -/
abbrev openComplementPullback :
    SheafOfModules 𝒪 ⥤
      SheafOfModules
        ((TopCat.Sheaf.pullback RingCat.{u} (openComplement Z).inclusion').obj 𝒪) :=
  OpenSubset.Restriction.functor (openComplement Z) 𝒪

/-- Direct image of module sheaves from the open complement. -/
abbrev openComplementPushforward :
    SheafOfModules
        ((TopCat.Sheaf.pullback RingCat.{u} (openComplement Z).inclusion').obj 𝒪) ⥤
      SheafOfModules 𝒪 :=
  SheafOfModules.pushforward (openComplementStructureMap 𝒪 Z)

/-- The canonical restriction map from a module sheaf to the direct image of its restriction to
the open complement. -/
abbrev restriction (F : SheafOfModules 𝒪) :
    F ⟶ (openComplementPushforward 𝒪 Z).obj ((openComplementPullback 𝒪 Z).obj F) :=
  (SheafOfModules.pullbackPushforwardAdjunction
    (openComplementStructureMap 𝒪 Z)).unit.app F

/-- The ambient endofunctor whose value is the kernel of restriction to the open complement. -/
@[stacks 0G6N "ambient closed-support kernel"]
noncomputable def ambientFunctor : SheafOfModules 𝒪 ⥤ SheafOfModules 𝒪 :=
  kernel (SheafOfModules.pullbackPushforwardAdjunction
    (openComplementStructureMap 𝒪 Z)).unit

/-- The natural inclusion of the ambient closed-support kernel into the identity functor. -/
noncomputable def ambientInclusion :
    ambientFunctor 𝒪 Z ⟶ 𝟭 (SheafOfModules 𝒪) :=
  kernel.ι (SheafOfModules.pullbackPushforwardAdjunction
    (openComplementStructureMap 𝒪 Z)).unit

/-- The ambient module sheaf of sections supported on the closed subset. -/
abbrev object (F : SheafOfModules 𝒪) : SheafOfModules 𝒪 :=
  (ambientFunctor 𝒪 Z).obj F

/-- The canonical inclusion of supported sections into the ambient module sheaf. -/
abbrev inclusion (F : SheafOfModules 𝒪) : object 𝒪 Z F ⟶ F :=
  (ambientInclusion 𝒪 Z).app F

/-- The closed-support kernel inclusion is a monomorphism. -/
noncomputable instance inclusionMono (F : SheafOfModules 𝒪) :
    Mono (inclusion 𝒪 Z F) := sorry

/-- The subobject of a module sheaf consisting of sections supported on the closed subset. -/
@[stacks 0G6N "closed-support subobject"]
noncomputable def subsheaf (F : SheafOfModules 𝒪) : Subobject F :=
  @Subobject.mk (SheafOfModules 𝒪) _ F (object 𝒪 Z F) (inclusion 𝒪 Z F)
    (inclusionMono 𝒪 Z F)

/-- The arrow of the closed-support subobject is its canonical kernel inclusion. -/
@[stacks 0G6N "closed-support subobject arrow"]
theorem subsheaf_arrow (F : SheafOfModules 𝒪) :
    (@Subobject.underlyingIso (SheafOfModules 𝒪) _ (object 𝒪 Z F) F
      (inclusion 𝒪 Z F) (inclusionMono 𝒪 Z F)).hom ≫ inclusion 𝒪 Z F =
      (subsheaf 𝒪 Z F).arrow := sorry

/-- The closed-support module sheaf restricted to the closed subspace. -/
def sheaf (F : SheafOfModules 𝒪) : ClosedSubset.Modules 𝒪 Z :=
  (ClosedSubset.pullback 𝒪 Z).obj (object 𝒪 Z F)

/-- The map on ambient closed-support kernels induced by a module-sheaf morphism. -/
abbrev subsheafMap {F G : SheafOfModules 𝒪} (f : F ⟶ G) :
    object 𝒪 Z F ⟶ object 𝒪 Z G :=
  (ambientFunctor 𝒪 Z).map f

/-- The functor of module sections supported on a closed subset. -/
@[stacks 0G6N "closed-support functor"]
noncomputable def functor : SheafOfModules 𝒪 ⥤ ClosedSubset.Modules 𝒪 Z :=
  ambientFunctor 𝒪 Z ⋙ ClosedSubset.pullback 𝒪 Z

@[inherit_doc]
scoped[SheafOfModules.ClosedSubset] notation:max "𝓗[" Z "]" =>
  SheafOfModules.ClosedSubset.SectionsWithSupport.functor _ Z

/-- Evaluation of the closed-support functor is restriction of the ambient kernel object. -/
@[simp]
theorem functor_obj (F : SheafOfModules 𝒪) :
    (functor 𝒪 Z).obj F = sheaf 𝒪 Z F := sorry

/-- The morphism part of the closed-support functor is induced by the ambient kernel functor. -/
@[simp]
theorem functor_map {F G : SheafOfModules 𝒪} (f : F ⟶ G) :
    (functor 𝒪 Z).map f = (ClosedSubset.pullback 𝒪 Z).map (subsheafMap 𝒪 Z f) := sorry

/-- On an open set, the canonical closed-support kernel inclusion has image exactly the sections
whose support is contained in the prescribed closed subset. -/
@[stacks 0G6N "sections of the canonical kernel"]
theorem inclusion_app_range (F : SheafOfModules 𝒪) (U : Opens X) :
    Set.range ((inclusion 𝒪 Z F).app U) =
      { s | localSectionSupport s ⊆ { x : U | x.1 ∈ Z } } := sorry

/-- A local section lies in the range of the canonical closed-support kernel inclusion exactly
when its support is contained in the prescribed closed subset. -/
theorem mem_range_inclusion_app_iff (F : SheafOfModules 𝒪) (U : Opens X)
    (s : F.val.obj (op U)) :
    s ∈ Set.range ((inclusion 𝒪 Z F).app U) ↔
      localSectionSupport s ⊆ { x : U | x.1 ∈ Z } := sorry

/-- The canonical closed-support kernel object is supported on the prescribed closed subset. -/
theorem object_support_subset (F : SheafOfModules 𝒪) :
    support (object 𝒪 Z F) ⊆ (Z : Set X) := sorry

/-- On an open set, the closed-support inclusion has image exactly the sections whose support is
contained in the prescribed closed subset. -/
@[stacks 0G6N "sections"]
theorem subsheaf_app_range (F : SheafOfModules 𝒪) (U : Opens X) :
    Set.range ((subsheaf 𝒪 Z F).arrow.val.app (op U)) =
      { s | localSectionSupport s ⊆ { x : U | x.1 ∈ Z } } := sorry

/-- A local section belongs to the closed-support subsheaf exactly when its support is contained
in the prescribed closed subset. -/
theorem mem_range_subsheaf_app_iff (F : SheafOfModules 𝒪) (U : Opens X)
    (s : F.val.obj (op U)) :
    s ∈ Set.range ((subsheaf 𝒪 Z F).arrow.val.app (op U)) ↔
      localSectionSupport s ⊆ { x : U | x.1 ∈ Z } := sorry

/-- The closed-support subobject is supported on the prescribed closed subset. -/
theorem subsheaf_support_subset (F : SheafOfModules 𝒪) :
    support (subsheaf 𝒪 Z F : SheafOfModules 𝒪) ⊆ (Z : Set X) := sorry

/-- The closed-support subobject is the largest subobject supported on the prescribed closed
subset. -/
@[stacks 0G6N "maximality"]
theorem le_subsheaf_of_support_subset {F : SheafOfModules 𝒪} (G : Subobject F)
    (hG : support (G : SheafOfModules 𝒪) ⊆ (Z : Set X)) :
    G ≤ subsheaf 𝒪 Z F := sorry

/-- The closed-support subobject is the greatest subobject whose
support is contained in the prescribed closed subset. -/
@[stacks 0G6N "greatest closed-support subobject"]
theorem isGreatest_subsheaf (F : SheafOfModules 𝒪) :
    IsGreatest
      { G : Subobject F | support (G : SheafOfModules 𝒪) ⊆ (Z : Set X) }
      (subsheaf 𝒪 Z F) := sorry

/-- The closed-support subobject of a module sheaf pushed forward from the closed subspace is the
whole subobject. -/
theorem subsheaf_pushforward_eq_top (F : ClosedSubset.Modules 𝒪 Z) :
    subsheaf 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F) = ⊤ := sorry

/-- The ambient closed-support inclusion is invertible on a module sheaf pushed forward from the
closed subspace. -/
@[stacks 0G6P "closed-support inclusion on a direct image is invertible"]
noncomputable instance inclusionPushforwardIsIso (F : ClosedSubset.Modules 𝒪 Z) :
    IsIso (inclusion 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F)) := sorry

/-- The pullback-pushforward counit is invertible on module sheaves over the closed subspace. -/
@[stacks 0G6P "closed-subspace pullback-pushforward counit is invertible"]
noncomputable instance pullbackPushforwardCounitAppIsIso
    (F : ClosedSubset.Modules 𝒪 Z) :
    IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).counit.app F) := sorry

/-- The pullback-pushforward unit is invertible on the ambient closed-support object. -/
@[stacks 0G6P "ambient closed-support pullback-pushforward unit is invertible"]
noncomputable instance objectPullbackPushforwardUnitAppIsIso (F : SheafOfModules 𝒪) :
    IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).unit.app (object 𝒪 Z F)) := sorry

/-- The explicit inverse of the closed-support inclusion on a direct image. -/
@[stacks 0G6P "inverse closed-support inclusion on a direct image"]
noncomputable def inclusionPushforwardInv (F : ClosedSubset.Modules 𝒪 Z)
    [h : IsIso (inclusion 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F))] :
    (ClosedSubset.pushforward 𝒪 Z).obj F ⟶
      object 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F) :=
  @CategoryTheory.inv _ _ _ _
    (inclusion 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F)) h

/-- The closed-support inclusion and its explicit inverse compose to the identity on the kernel
object. -/
@[simp, stacks 0G6P "closed-support inclusion forward-inverse law"]
theorem inclusionPushforward_hom_inv_id (F : ClosedSubset.Modules 𝒪 Z)
    [IsIso (inclusion 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F))] :
    inclusion 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F) ≫
        inclusionPushforwardInv 𝒪 Z F = 𝟙 _ := sorry

/-- The explicit inverse of the closed-support inclusion followed by the inclusion is the
identity on a direct image. -/
@[simp, stacks 0G6P "closed-support inclusion inverse-forward law"]
theorem inclusionPushforward_inv_hom_id (F : ClosedSubset.Modules 𝒪 Z)
    [IsIso (inclusion 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F))] :
    inclusionPushforwardInv 𝒪 Z F ≫
        inclusion 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F) = 𝟙 _ := sorry

/-- The closed-support inclusion on a direct image is a literal isomorphism. -/
@[stacks 0G6P "closed-support inclusion isomorphism on a direct image"]
noncomputable def inclusionPushforwardIso (F : ClosedSubset.Modules 𝒪 Z)
    [IsIso (inclusion 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F))] :
    object 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F) ≅
      (ClosedSubset.pushforward 𝒪 Z).obj F where
  hom := inclusion 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F)
  inv := inclusionPushforwardInv 𝒪 Z F
  hom_inv_id := inclusionPushforward_hom_inv_id 𝒪 Z F
  inv_hom_id := inclusionPushforward_inv_hom_id 𝒪 Z F

/-- The forward map of `inclusionPushforwardIso` is the closed-support inclusion. -/
@[simp, stacks 0G6P "closed-support inclusion isomorphism hom"]
theorem inclusionPushforwardIso_hom (F : ClosedSubset.Modules 𝒪 Z)
    [IsIso (inclusion 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F))] :
    (inclusionPushforwardIso 𝒪 Z F).hom =
      inclusion 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F) := sorry

/-- The inverse map of `inclusionPushforwardIso` is the explicit closed-support inverse. -/
@[simp, stacks 0G6P "closed-support inclusion isomorphism inverse"]
theorem inclusionPushforwardIso_inv (F : ClosedSubset.Modules 𝒪 Z)
    [IsIso (inclusion 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F))] :
    (inclusionPushforwardIso 𝒪 Z F).inv = inclusionPushforwardInv 𝒪 Z F := sorry

/-- The explicit inverse of the pullback-pushforward counit on a closed-subspace module. -/
@[stacks 0G6P "inverse closed-subspace pullback-pushforward counit"]
noncomputable def pullbackPushforwardCounitAppInv (F : ClosedSubset.Modules 𝒪 Z)
    [h : IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).counit.app F)] :
    F ⟶ (ClosedSubset.pullback 𝒪 Z).obj
      ((ClosedSubset.pushforward 𝒪 Z).obj F) :=
  @CategoryTheory.inv _ _ _ _
    ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).counit.app F) h

/-- The pullback-pushforward counit followed by its explicit inverse is the identity. -/
@[simp, stacks 0G6P "closed-subspace counit forward-inverse law"]
theorem pullbackPushforwardCounitApp_hom_inv_id (F : ClosedSubset.Modules 𝒪 Z)
    [IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).counit.app F)] :
    (SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).counit.app F ≫
        pullbackPushforwardCounitAppInv 𝒪 Z F = 𝟙 _ := sorry

/-- The explicit inverse of the pullback-pushforward counit followed by the counit is the
identity. -/
@[simp, stacks 0G6P "closed-subspace counit inverse-forward law"]
theorem pullbackPushforwardCounitApp_inv_hom_id (F : ClosedSubset.Modules 𝒪 Z)
    [IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).counit.app F)] :
    pullbackPushforwardCounitAppInv 𝒪 Z F ≫
        (SheafOfModules.pullbackPushforwardAdjunction
          (ClosedSubset.structureMap 𝒪 Z)).counit.app F = 𝟙 _ := sorry

/-- The pullback-pushforward counit on a closed-subspace module is a literal isomorphism. -/
@[stacks 0G6P "closed-subspace pullback-pushforward counit isomorphism"]
noncomputable def pullbackPushforwardCounitAppIso (F : ClosedSubset.Modules 𝒪 Z)
    [IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).counit.app F)] :
    (ClosedSubset.pullback 𝒪 Z).obj ((ClosedSubset.pushforward 𝒪 Z).obj F) ≅ F where
  hom := (SheafOfModules.pullbackPushforwardAdjunction
    (ClosedSubset.structureMap 𝒪 Z)).counit.app F
  inv := pullbackPushforwardCounitAppInv 𝒪 Z F
  hom_inv_id := pullbackPushforwardCounitApp_hom_inv_id 𝒪 Z F
  inv_hom_id := pullbackPushforwardCounitApp_inv_hom_id 𝒪 Z F

/-- The forward map of `pullbackPushforwardCounitAppIso` is the adjunction counit. -/
@[simp, stacks 0G6P "closed-subspace counit isomorphism hom"]
theorem pullbackPushforwardCounitAppIso_hom (F : ClosedSubset.Modules 𝒪 Z)
    [IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).counit.app F)] :
    (pullbackPushforwardCounitAppIso 𝒪 Z F).hom =
      (SheafOfModules.pullbackPushforwardAdjunction
        (ClosedSubset.structureMap 𝒪 Z)).counit.app F := sorry

/-- The inverse map of `pullbackPushforwardCounitAppIso` is explicit. -/
@[simp, stacks 0G6P "closed-subspace counit isomorphism inverse"]
theorem pullbackPushforwardCounitAppIso_inv (F : ClosedSubset.Modules 𝒪 Z)
    [IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).counit.app F)] :
    (pullbackPushforwardCounitAppIso 𝒪 Z F).inv =
      pullbackPushforwardCounitAppInv 𝒪 Z F := sorry

/-- The explicit inverse of the pullback-pushforward unit on the ambient closed-support object.
-/
@[stacks 0G6P "inverse ambient closed-support pullback-pushforward unit"]
noncomputable def objectPullbackPushforwardUnitAppInv (F : SheafOfModules 𝒪)
    [h : IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).unit.app (object 𝒪 Z F))] :
    (ClosedSubset.pushforward 𝒪 Z).obj
        ((ClosedSubset.pullback 𝒪 Z).obj (object 𝒪 Z F)) ⟶ object 𝒪 Z F :=
  @CategoryTheory.inv _ _ _ _
    ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).unit.app (object 𝒪 Z F)) h

/-- The pullback-pushforward unit followed by its explicit inverse is the identity. -/
@[simp, stacks 0G6P "ambient closed-support unit forward-inverse law"]
theorem objectPullbackPushforwardUnitApp_hom_inv_id (F : SheafOfModules 𝒪)
    [IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).unit.app (object 𝒪 Z F))] :
    (SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).unit.app (object 𝒪 Z F) ≫
        objectPullbackPushforwardUnitAppInv 𝒪 Z F = 𝟙 _ := sorry

/-- The explicit inverse of the pullback-pushforward unit followed by the unit is the identity.
-/
@[simp, stacks 0G6P "ambient closed-support unit inverse-forward law"]
theorem objectPullbackPushforwardUnitApp_inv_hom_id (F : SheafOfModules 𝒪)
    [IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).unit.app (object 𝒪 Z F))] :
    objectPullbackPushforwardUnitAppInv 𝒪 Z F ≫
        (SheafOfModules.pullbackPushforwardAdjunction
          (ClosedSubset.structureMap 𝒪 Z)).unit.app (object 𝒪 Z F) = 𝟙 _ := sorry

/-- The pullback-pushforward unit on the ambient closed-support object is a literal isomorphism.
-/
@[stacks 0G6P "ambient closed-support pullback-pushforward unit isomorphism"]
noncomputable def objectPullbackPushforwardUnitAppIso (F : SheafOfModules 𝒪)
    [IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).unit.app (object 𝒪 Z F))] :
    object 𝒪 Z F ≅
      (ClosedSubset.pushforward 𝒪 Z).obj
        ((ClosedSubset.pullback 𝒪 Z).obj (object 𝒪 Z F)) where
  hom := (SheafOfModules.pullbackPushforwardAdjunction
    (ClosedSubset.structureMap 𝒪 Z)).unit.app (object 𝒪 Z F)
  inv := objectPullbackPushforwardUnitAppInv 𝒪 Z F
  hom_inv_id := objectPullbackPushforwardUnitApp_hom_inv_id 𝒪 Z F
  inv_hom_id := objectPullbackPushforwardUnitApp_inv_hom_id 𝒪 Z F

/-- The forward map of `objectPullbackPushforwardUnitAppIso` is the adjunction unit. -/
@[simp, stacks 0G6P "ambient closed-support unit isomorphism hom"]
theorem objectPullbackPushforwardUnitAppIso_hom (F : SheafOfModules 𝒪)
    [IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).unit.app (object 𝒪 Z F))] :
    (objectPullbackPushforwardUnitAppIso 𝒪 Z F).hom =
      (SheafOfModules.pullbackPushforwardAdjunction
        (ClosedSubset.structureMap 𝒪 Z)).unit.app (object 𝒪 Z F) := sorry

/-- The inverse map of `objectPullbackPushforwardUnitAppIso` is explicit. -/
@[simp, stacks 0G6P "ambient closed-support unit isomorphism inverse"]
theorem objectPullbackPushforwardUnitAppIso_inv (F : SheafOfModules 𝒪)
    [IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).unit.app (object 𝒪 Z F))] :
    (objectPullbackPushforwardUnitAppIso 𝒪 Z F).inv =
      objectPullbackPushforwardUnitAppInv 𝒪 Z F := sorry

/-- The unit component for direct image left adjoint to closed support, given the
invertibility data used to construct it. -/
@[stacks 0G6P "closed-support adjunction unit component from isomorphisms"]
noncomputable def adjunctionUnitAppOfIso (F : ClosedSubset.Modules 𝒪 Z)
    [hc : IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).counit.app F)]
    [hi : IsIso (inclusion 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F))] :
    F ⟶ (functor 𝒪 Z).obj ((ClosedSubset.pushforward 𝒪 Z).obj F) :=
  @pullbackPushforwardCounitAppInv _ 𝒪 Z F hc ≫
      (ClosedSubset.pullback 𝒪 Z).map
        (@inclusionPushforwardInv _ 𝒪 Z F hi)

/-- The counit component for direct image left adjoint to closed support, given
the invertibility data used to construct it. -/
@[stacks 0G6P "closed-support adjunction counit component from isomorphisms"]
noncomputable def adjunctionCounitAppOfIso (F : SheafOfModules 𝒪)
    [hu : IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).unit.app (object 𝒪 Z F))] :
  (ClosedSubset.pushforward 𝒪 Z).obj ((functor 𝒪 Z).obj F) ⟶ F :=
  @objectPullbackPushforwardUnitAppInv _ 𝒪 Z F hu ≫
      inclusion 𝒪 Z F

/-- The unit component for direct image left adjoint to closed support, using
the canonical invertibility instances. -/
@[stacks 0G6P "closed-support adjunction unit component"]
noncomputable def adjunctionUnitApp (F : ClosedSubset.Modules 𝒪 Z) :
    F ⟶ (functor 𝒪 Z).obj ((ClosedSubset.pushforward 𝒪 Z).obj F) :=
  adjunctionUnitAppOfIso 𝒪 Z F

/-- The counit component for direct image left adjoint to closed support, using
the canonical invertibility instance. -/
@[stacks 0G6P "closed-support adjunction counit component"]
noncomputable def adjunctionCounitApp (F : SheafOfModules 𝒪) :
    (ClosedSubset.pushforward 𝒪 Z).obj ((functor 𝒪 Z).obj F) ⟶ F :=
  adjunctionCounitAppOfIso 𝒪 Z F

/-- Direct image from a closed subspace is left adjoint to module sections
supported on that subspace. -/
@[stacks 0G6P]
noncomputable def adjunction : ClosedSubset.pushforward 𝒪 Z ⊣ functor 𝒪 Z where
  unit :=
    { app := adjunctionUnitApp 𝒪 Z
      naturality := sorry }
  counit :=
    { app := adjunctionCounitApp 𝒪 Z
      naturality := sorry }
  left_triangle_components := sorry
  right_triangle_components := sorry

/-- The unit of the closed-support adjunction is the explicit unit component. -/
@[stacks 0G6P "closed-support adjunction unit component recall"]
theorem adjunction_unit_app (F : ClosedSubset.Modules 𝒪 Z) :
    (adjunction 𝒪 Z).unit.app F = adjunctionUnitApp 𝒪 Z F := sorry

/-- The counit of the closed-support adjunction is the explicit counit component. -/
@[stacks 0G6P "closed-support adjunction counit component recall"]
theorem adjunction_counit_app (F : SheafOfModules 𝒪) :
    (adjunction 𝒪 Z).counit.app F = adjunctionCounitApp 𝒪 Z F := sorry

/-- The pullback-pushforward counit for a bundled closed subspace is an isomorphism. -/
noncomputable instance pullbackPushforwardCounitIsIso :
    IsIso (SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).counit := sorry

/-- Direct image from a bundled closed subspace is fully faithful. -/
@[stacks 0G6P "closed-subset pushforward is fully faithful"]
noncomputable def pushforwardFullyFaithful :
    (ClosedSubset.pushforward 𝒪 Z).FullyFaithful :=
  (SheafOfModules.pullbackPushforwardAdjunction
    (ClosedSubset.structureMap 𝒪 Z)).fullyFaithfulROfIsIsoCounit

/-- Direct image from a bundled closed subspace is canonically a left adjoint. -/
@[stacks 0G6P "closed-subset pushforward is a left adjoint"]
noncomputable instance pushforwardIsLeftAdjoint :
    (ClosedSubset.pushforward 𝒪 Z).IsLeftAdjoint := sorry

/-- Direct image from a bundled closed subspace is canonically a right adjoint. -/
noncomputable instance pushforwardIsRightAdjoint :
    (ClosedSubset.pushforward 𝒪 Z).IsRightAdjoint := sorry

/-- Direct image from a bundled closed subspace preserves finite limits. -/
noncomputable instance pushforwardPreservesFiniteLimits :
    PreservesFiniteLimits (ClosedSubset.pushforward 𝒪 Z) := sorry

/-- Direct image from a bundled closed subspace preserves finite colimits. -/
noncomputable instance pushforwardPreservesFiniteColimits :
    PreservesFiniteColimits (ClosedSubset.pushforward 𝒪 Z) := sorry

/-- Direct image of module sheaves from a bundled closed subspace is exact. -/
@[stacks 0G6P "closed-subset module pushforward is exact"]
theorem pushforwardExact :
    exactFunctor (ClosedSubset.Modules 𝒪 Z) (SheafOfModules 𝒪)
      (ClosedSubset.pushforward 𝒪 Z) := sorry

/-- The closed-support functor is canonically a right adjoint. -/
noncomputable instance functorIsRightAdjoint : (functor 𝒪 Z).IsRightAdjoint :=
  (adjunction 𝒪 Z).isRightAdjoint

/-- The closed-support functor is additive. -/
noncomputable instance functorAdditive : (functor 𝒪 Z).Additive := sorry

/-- The closed-support functor is left exact. -/
@[stacks 0G6N "left exact"]
theorem functor_leftExact :
    leftExactFunctor (SheafOfModules 𝒪) (ClosedSubset.Modules 𝒪 Z) (functor 𝒪 Z) := sorry

/-- A functor of module sections supported on a closed subset need not be exact. -/
@[stacks 0G6N "not exact in general"]
theorem exists_not_exact :
    ∃ (X : TopCat.{u}) (𝒪 : X.Sheaf RingCat.{u}) (Z : Closeds X),
      ¬ exactFunctor (SheafOfModules 𝒪) (ClosedSubset.Modules 𝒪 Z) (functor 𝒪 Z) := sorry

end SheafOfModules.ClosedSubset.SectionsWithSupport
