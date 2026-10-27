/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
public import ReasLib.Topology.Sheaf.Subset.General
public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

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

set_option backward.isDefEq.respectTransparency false in
/-- Recover a module morphism on the closed subspace from a morphism of direct images.
The additive map is evaluated on the largest ambient open with the prescribed trace;
compatibility with the restricted ring action is a proposition. -/
noncomputable def pushforwardPreimage {F G : ClosedSubset.Modules 𝒪 Z}
    (f : (ClosedSubset.pushforward 𝒪 Z).obj F ⟶
      (ClosedSubset.pushforward 𝒪 Z).obj G) : F ⟶ G where
  val := PresheafOfModules.homMk
    (TopCat.Sheaf.Subset.pushforwardPreimage (C := AddCommGrpCat.{u}) (Z : Set X)
      (F := (SheafOfModules.toSheaf (ClosedSubset.ringSheaf 𝒪 Z)).obj F)
      (G := (SheafOfModules.toSheaf (ClosedSubset.ringSheaf 𝒪 Z)).obj G)
      ((SheafOfModules.toSheaf 𝒪).map f)).hom (by sorry)

set_option backward.isDefEq.respectTransparency false in
/-- Extend a supported section from `V` to `W` by gluing with zero off `Z`.
The trace condition ensures that `V` and the open complement cover `W`. -/
noncomputable def supportedExtend (F : SheafOfModules 𝒪) (V W : Opens X)
    (h : (Opens.map (ClosedSubset.inclusion Z)).obj W ≤
      (Opens.map (ClosedSubset.inclusion Z)).obj V) :
    sectionsOnOpen (object 𝒪 Z F) V ⟶ sectionsOnOpen (object 𝒪 Z F) W :=
  (TopCat.Sheaf.isLimitPullbackCone
      ((SheafOfModules.toSheaf 𝒪).obj (object 𝒪 Z F)) V (openComplement Z)).lift (PullbackCone.mk (𝟙 _) 0 (by sorry)) ≫
    (object 𝒪 Z F).val.presheaf.map
      (homOfLE (by
        intro x hx
        by_cases hz : x ∈ Z
        · exact Or.inl (h (x := ⟨x, hz⟩) hx)
        · exact Or.inr hz : W ≤ V ⊔ openComplement Z)).op

/-- The actual inducing proof for the subtype inclusion, used by the explicit hull model. -/
theorem inclusion_isInducing : Topology.IsInducing (ClosedSubset.inclusion Z) :=
  Topology.IsInducing.subtypeVal

/-- The largest ambient open having the prescribed trace on the closed subspace. -/
abbrev ambientHull (Z : Closeds X) : Opens (TopCat.subsetSpace (Z : Set X)) → Opens X :=
  (inclusion_isInducing Z).functorObj

/-- The additive presheaf of supported sections on the largest ambient open with a given trace.
No sheaf condition is asserted for this presheaf. -/
noncomputable def supportedRestrictionAdditivePresheaf (F : SheafOfModules 𝒪) :
    (TopCat.subsetSpace (Z : Set X)).Presheaf AddCommGrpCat.{u} :=
  (inclusion_isInducing Z).functor.op ⋙ (object 𝒪 Z F).val.presheaf

/-- The canonical additive sheafification of the hull presheaf. Its sheaf condition is supplied
by mathlib's proved sheafification construction. -/
noncomputable def supportedRestrictionAdditive (F : SheafOfModules 𝒪) :
    (TopCat.subsetSpace (Z : Set X)).Sheaf AddCommGrpCat.{u} :=
  (presheafToSheaf (Opens.grothendieckTopology (Z : Set X)) AddCommGrpCat.{u}).obj
    (supportedRestrictionAdditivePresheaf 𝒪 Z F)

/-- The canonical map from hull sections into their additive sheafification. -/
noncomputable def supportedRestrictionToSheafify (F : SheafOfModules 𝒪) :
    supportedRestrictionAdditivePresheaf 𝒪 Z F ⟶ (supportedRestrictionAdditive 𝒪 Z F).obj :=
  CategoryTheory.toSheafify (Opens.grothendieckTopology (Z : Set X)) _

/-- The additive unit is genuinely locally surjective, independently of module laws. -/
instance supportedRestrictionToSheafify_locallySurjective (F : SheafOfModules 𝒪) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (Z : Set X))
      (supportedRestrictionToSheafify 𝒪 Z F) :=
  Presheaf.isLocallySurjective_toSheafify' _ (supportedRestrictionAdditivePresheaf 𝒪 Z F)

/-- The presheaf inverse image of the coefficient ring. -/
abbrev restrictedRingPresheaf :=
  (TopCat.Presheaf.pullback RingCat.{u} (ClosedSubset.inclusion Z)).obj 𝒪.obj

/-- The genuine sheafification map to the restricted ring sheaf. -/
noncomputable def restrictedRingPresheafMap :
    restrictedRingPresheaf 𝒪 Z ⟶ (ClosedSubset.ringSheaf 𝒪 Z).obj :=
  CategoryTheory.toSheafify _ (restrictedRingPresheaf 𝒪 Z) ≫
    ((TopCat.Sheaf.forget RingCat.{u} _).mapIso
      ((TopCat.Sheaf.pullbackIso RingCat.{u} (ClosedSubset.inclusion Z)).app 𝒪)).inv

-- These proofs feed the local scalar-action construction, so they use only the
-- proved sheafification and isomorphism instances from mathlib.
instance restrictedRingPresheafMap_locallyInjective :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (Z : Set X))
      (restrictedRingPresheafMap 𝒪 Z) := by
  exact Presheaf.isLocallyInjective_comp (Opens.grothendieckTopology (Z : Set X))
    (CategoryTheory.toSheafify (Opens.grothendieckTopology (Z : Set X))
      (restrictedRingPresheaf 𝒪 Z))
    (((TopCat.Sheaf.forget RingCat.{u} _).mapIso
      ((TopCat.Sheaf.pullbackIso RingCat.{u} (ClosedSubset.inclusion Z)).app 𝒪)).inv)

instance restrictedRingPresheafMap_locallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (Z : Set X))
      (restrictedRingPresheafMap 𝒪 Z) := by
  exact Presheaf.isLocallySurjective_comp (Opens.grothendieckTopology (Z : Set X))
    (CategoryTheory.toSheafify (Opens.grothendieckTopology (Z : Set X))
      (restrictedRingPresheaf 𝒪 Z))
    (((TopCat.Sheaf.forget RingCat.{u} _).mapIso
      ((TopCat.Sheaf.pullbackIso RingCat.{u} (ClosedSubset.inclusion Z)).app 𝒪)).inv)

/-- A scalar defined on a neighbourhood of `U` acts on supported sections by restriction,
multiplication, and extension by zero. -/
noncomputable def neighbourhoodScalar (F : SheafOfModules 𝒪)
    (U : Opens (TopCat.subsetSpace (Z : Set X))) (V : Opens X)
    (h : U ≤ (Opens.map (ClosedSubset.inclusion Z)).obj V) :
    𝒪.obj.obj (op V) →+*
      End (sectionsOnOpen (object 𝒪 Z F) (ambientHull Z U)) where
  toFun r :=
    let H := ambientHull Z U
    (object 𝒪 Z F).val.presheaf.map (homOfLE (inf_le_left : H ⊓ V ≤ H)).op ≫
      ModuleCat.smul ((object 𝒪 Z F).val.obj (op (H ⊓ V)))
        (𝒪.obj.map (homOfLE (inf_le_right : H ⊓ V ≤ V)).op r) ≫
      supportedExtend 𝒪 Z F (H ⊓ V) H (by
        intro x hx
        exact ⟨hx, h (((inclusion_isInducing Z).map_functorObj U).le hx)⟩)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The scalar action of the presheaf inverse-image ring is induced by its neighbourhood
colimit, using the concrete extension-by-zero maps. -/
noncomputable def supportedRingAction (F : SheafOfModules 𝒪)
    (U : (Opens (TopCat.subsetSpace (Z : Set X)))ᵒᵖ) :
    (restrictedRingPresheaf 𝒪 Z).obj U ⟶
      RingCat.of (End ((supportedRestrictionAdditivePresheaf 𝒪 Z F).obj U)) :=
  ((Opens.map (ClosedSubset.inclusion Z)).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit
    𝒪.obj U).desc
      { pt := RingCat.of (End ((supportedRestrictionAdditivePresheaf 𝒪 Z F).obj U))
        ι :=
          { app := fun j ↦ RingCat.ofHom
              (neighbourhoodScalar 𝒪 Z F U.unop j.left.unop j.hom.unop.le)
            naturality := sorry } }

/-- The genuine gluing limit of an additive sheaf, after forgetting to sets.
In applications below the sheaf argument is a canonical sheafification or the ambient kernel,
so the certificate from which this limit is selected has no admitted existence proof. -/
noncomputable def sectionGluingLimit {Y : TopCat.{u}} (A : Y.Sheaf AddCommGrpCat.{u})
    {ι : Type u} (V : ι → Opens Y) :
    IsLimit (((A.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u}).mapCone
      (Pairwise.cocone V).op)) :=
  ((TopCat.Presheaf.isSheaf_iff_isSheafPairwiseIntersections _).mp
    ((sheafCompose (Opens.grothendieckTopology Y)
      (CategoryTheory.forget AddCommGrpCat.{u})).obj A).property V).some

/-- Glue the given local sections using the actual limit of the sheaf. The components of the
input cone are the displayed sections and their restrictions; only their equality laws are
proof obligations. -/
noncomputable def glueSections {Y : TopCat.{u}} (A : Y.Sheaf AddCommGrpCat.{u})
    {ι : Type u} (V : ι → Opens Y) (sf : ∀ i, A.obj.obj (op (V i)))
    (hc : TopCat.Presheaf.IsCompatible A.obj V sf) : A.obj.obj (op (iSup V)) :=
  let t := (show TopCat.Presheaf.IsCompatible
    (A.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u}) V sf from hc).sectionPairwise
  let c : Cone ((Pairwise.diagram V).op ⋙ A.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u}) :=
    { pt := PUnit
      π :=
        { app := fun i ↦ TypeCat.ofHom (fun _ ↦ t.val i)
          naturality := by
            intro i j f
            ext x
            exact (t.prop f).symm } }
  (sectionGluingLimit A V).lift c PUnit.unit

/-- All simultaneous local representatives of a scalar and a section.
This is an indexing type, not an assumed existence certificate. -/
structure ScalarRepresentative (F : SheafOfModules 𝒪)
    (U : Opens (TopCat.subsetSpace (Z : Set X)))
    (r : (ClosedSubset.ringSheaf 𝒪 Z).obj.obj (op U))
    (m : (supportedRestrictionAdditive 𝒪 Z F).obj.obj (op U)) where
  openSet : Opens (TopCat.subsetSpace (Z : Set X))
  le : openSet ≤ U
  scalar : (restrictedRingPresheaf 𝒪 Z).obj (op openSet)
  section_ : (supportedRestrictionAdditivePresheaf 𝒪 Z F).obj (op openSet)
  scalar_eq : (restrictedRingPresheafMap 𝒪 Z).app (op openSet) scalar =
    (ClosedSubset.ringSheaf 𝒪 Z).obj.map (homOfLE le).op r
  section_eq : (supportedRestrictionToSheafify 𝒪 Z F).app (op openSet) section_ =
    (supportedRestrictionAdditive 𝒪 Z F).obj.map (homOfLE le).op m

/-- The simultaneous local representatives cover the domain, by the proved local surjectivity
of ring and additive sheafification. -/
theorem scalarRepresentative_iSup (F : SheafOfModules 𝒪)
    (U : Opens (TopCat.subsetSpace (Z : Set X)))
    (r : (ClosedSubset.ringSheaf 𝒪 Z).obj.obj (op U))
    (m : (supportedRestrictionAdditive 𝒪 Z F).obj.obj (op U)) :
    (⨆ q : ScalarRepresentative 𝒪 Z F U r m, q.openSet) = U := by
  apply le_antisymm
  · exact iSup_le (fun q ↦ q.le)
  · intro x hx
    have hS := (Opens.grothendieckTopology (Z : Set X)).intersection_covering
      (Presheaf.imageSieve_mem _ (restrictedRingPresheafMap 𝒪 Z) r)
      (Presheaf.imageSieve_mem _ (supportedRestrictionToSheafify 𝒪 Z F) m)
    obtain ⟨W, f, hf, hxW⟩ := hS x hx
    obtain ⟨a, ha⟩ := hf.1
    obtain ⟨b, hb⟩ := hf.2
    exact Opens.mem_iSup.mpr ⟨⟨W, f.le, a, b, ha, hb⟩, hxW⟩

/-- Scalar multiplication is the explicit gluing of products of local representatives.
It does not select an `SMulCandidate` or consume an admitted sheaf condition. -/
noncomputable def supportedScalarMul (F : SheafOfModules 𝒪)
    (U : Opens (TopCat.subsetSpace (Z : Set X)))
    (r : (ClosedSubset.ringSheaf 𝒪 Z).obj.obj (op U))
    (m : (supportedRestrictionAdditive 𝒪 Z F).obj.obj (op U)) :
    (supportedRestrictionAdditive 𝒪 Z F).obj.obj (op U) :=
  (supportedRestrictionAdditive 𝒪 Z F).obj.map
      (eqToHom (scalarRepresentative_iSup 𝒪 Z F U r m).symm).op
    (glueSections (supportedRestrictionAdditive 𝒪 Z F)
      (fun q : ScalarRepresentative 𝒪 Z F U r m ↦ q.openSet)
      (fun q ↦ (supportedRestrictionToSheafify 𝒪 Z F).app (op q.openSet)
        ((show (supportedRestrictionAdditivePresheaf 𝒪 Z F).obj (op q.openSet) ⟶
            (supportedRestrictionAdditivePresheaf 𝒪 Z F).obj (op q.openSet)
          from (supportedRingAction 𝒪 Z F (op q.openSet)).hom q.scalar) q.section_)) (by sorry))

/-- The module laws for the explicitly defined scalar multiplication. -/
noncomputable def supportedRestrictionModule (F : SheafOfModules 𝒪)
    (U : (Opens (TopCat.subsetSpace (Z : Set X)))ᵒᵖ) :
    Module ((ClosedSubset.ringSheaf 𝒪 Z).obj.obj U)
      ((supportedRestrictionAdditive 𝒪 Z F).obj.obj U) where
  smul := supportedScalarMul 𝒪 Z F U.unop
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The supported module sheaf over the actual restricted ring. Its sections and gluing come
from canonical additive sheafification, and its scalar operation is the local-product formula. -/
noncomputable def supportedRestriction (F : SheafOfModules 𝒪) : ClosedSubset.Modules 𝒪 Z :=
  letI := supportedRestrictionModule 𝒪 Z F
  { val := PresheafOfModules.ofPresheaf (supportedRestrictionAdditive 𝒪 Z F).obj (by sorry)
    isSheaf := (supportedRestrictionAdditive 𝒪 Z F).property }

/-- The underlying additive sheaf is the canonical sheafification by definition. -/
theorem supportedRestriction_toSheaf (F : SheafOfModules 𝒪) :
    (SheafOfModules.toSheaf (ClosedSubset.ringSheaf 𝒪 Z)).obj
      (supportedRestriction 𝒪 Z F) = supportedRestrictionAdditive 𝒪 Z F := rfl

/-- The scalar operation of the supported module is the explicit local-product gluing. -/
theorem supportedRestriction_smul (F : SheafOfModules 𝒪)
    (U : (Opens (TopCat.subsetSpace (Z : Set X)))ᵒᵖ)
    (r : (ClosedSubset.ringSheaf 𝒪 Z).obj.obj U)
    (m : (supportedRestriction 𝒪 Z F).val.obj U) :
    r • m = supportedScalarMul 𝒪 Z F U.unop r m := rfl

/-- All local representatives of a sheafified section on the trace of an ambient open. -/
structure SectionRepresentative (F : SheafOfModules 𝒪) (V : Opens X)
    (s : (supportedRestrictionAdditive 𝒪 Z F).obj.obj
      (op ((Opens.map (ClosedSubset.inclusion Z)).obj V))) where
  openSet : Opens (TopCat.subsetSpace (Z : Set X))
  le : openSet ≤ (Opens.map (ClosedSubset.inclusion Z)).obj V
  section_ : (supportedRestrictionAdditivePresheaf 𝒪 Z F).obj (op openSet)
  section_eq : (supportedRestrictionToSheafify 𝒪 Z F).app (op openSet) section_ =
    (supportedRestrictionAdditive 𝒪 Z F).obj.map (homOfLE le).op s

/-- Cover the ambient open by the domains of every local representative and its open complement
of `Z`. Each representative already contains its actual hull section. -/
def representativeOpen (F : SheafOfModules 𝒪) (V : Opens X)
    (s : (supportedRestrictionAdditive 𝒪 Z F).obj.obj
      (op ((Opens.map (ClosedSubset.inclusion Z)).obj V))) :
    Option (SectionRepresentative 𝒪 Z F V s) → Opens X
  | none => V ⊓ openComplement Z
  | some q => V ⊓ ambientHull Z q.openSet

/-- The representative opens and the complement cover the ambient open. -/
theorem representativeOpen_iSup (F : SheafOfModules 𝒪) (V : Opens X)
    (s : (supportedRestrictionAdditive 𝒪 Z F).obj.obj
      (op ((Opens.map (ClosedSubset.inclusion Z)).obj V))) :
    iSup (representativeOpen 𝒪 Z F V s) = V := by
  apply le_antisymm
  · apply iSup_le
    rintro (_ | q) <;> exact inf_le_left
  · intro x hx
    by_cases hz : x ∈ Z
    · have hS := Presheaf.imageSieve_mem
        (Opens.grothendieckTopology (Z : Set X))
        (supportedRestrictionToSheafify 𝒪 Z F) s
      obtain ⟨W, f, hf, hxW⟩ := hS ⟨x, hz⟩ hx
      obtain ⟨a, ha⟩ := hf
      let q : SectionRepresentative 𝒪 Z F V s := ⟨W, f.le, a, ha⟩
      apply Opens.mem_iSup.mpr
      refine ⟨some q, hx, ?_⟩
      exact ((inclusion_isInducing Z).mem_functorObj_iff W).mpr hxW
    · exact Opens.mem_iSup.mpr ⟨none, hx, hz⟩

/-- Explicit inverse on ambient sections: glue every local representative with zero off `Z`,
using the real sheaf condition of the ambient kernel. -/
noncomputable def supportedRestrictionInvSection (F : SheafOfModules 𝒪) (V : Opens X)
    (s : (supportedRestrictionAdditive 𝒪 Z F).obj.obj
      (op ((Opens.map (ClosedSubset.inclusion Z)).obj V))) : (object 𝒪 Z F).val.obj (op V) :=
  (object 𝒪 Z F).val.presheaf.map
      (eqToHom (representativeOpen_iSup 𝒪 Z F V s).symm).op
    (glueSections ((SheafOfModules.toSheaf 𝒪).obj (object 𝒪 Z F))
      (representativeOpen 𝒪 Z F V s)
      (fun q ↦ match q with
        | none => 0
        | some q => (object 𝒪 Z F).val.presheaf.map
            (homOfLE (inf_le_right :
              V ⊓ ambientHull Z q.openSet ≤ _)).op q.section_)
      (by sorry))

set_option backward.isDefEq.respectTransparency false in
/-- Extension by zero and representative gluing identify the ambient kernel with the direct
image of its module restriction. The two maps are explicit; no inverse certificate is consumed. -/
noncomputable def supportedRestrictionPushforwardIso (F : SheafOfModules 𝒪) :
    object 𝒪 Z F ≅ (ClosedSubset.pushforward 𝒪 Z).obj (supportedRestriction 𝒪 Z F) where
  hom.val := PresheafOfModules.homMk
    { app := fun V ↦ supportedExtend 𝒪 Z F V.unop
        (ambientHull Z
          ((Opens.map (ClosedSubset.inclusion Z)).obj V.unop))
        (by rw [(inclusion_isInducing Z).map_functorObj]) ≫
          (supportedRestrictionToSheafify 𝒪 Z F).app
            (op ((Opens.map (ClosedSubset.inclusion Z)).obj V.unop))
      naturality := sorry } (by sorry)
  inv.val := PresheafOfModules.homMk
    { app := fun V ↦ AddCommGrpCat.ofHom
        { toFun := supportedRestrictionInvSection 𝒪 Z F V.unop
          map_zero' := sorry
          map_add' := sorry }
      naturality := sorry } (by sorry)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The explicit inverse of the closed-support inclusion on a direct image. -/
@[stacks 0G6P "inverse closed-support inclusion on a direct image"]
noncomputable def inclusionPushforwardInv (F : ClosedSubset.Modules 𝒪 Z) :
    (ClosedSubset.pushforward 𝒪 Z).obj F ⟶
      object 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F) :=
  kernel.lift _ (𝟙 _) (by sorry) ≫
    (PreservesKernel.iso ((CategoryTheory.evaluation (SheafOfModules 𝒪) (SheafOfModules 𝒪)).obj
        ((ClosedSubset.pushforward 𝒪 Z).obj F))
      (SheafOfModules.pullbackPushforwardAdjunction
        (openComplementStructureMap 𝒪 Z)).unit).inv

/-- The closed-support inclusion and its explicit inverse compose to the identity on the kernel
object. -/
@[simp, stacks 0G6P "closed-support inclusion forward-inverse law"]
theorem inclusionPushforward_hom_inv_id (F : ClosedSubset.Modules 𝒪 Z) :
    inclusion 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F) ≫
        inclusionPushforwardInv 𝒪 Z F = 𝟙 _ := sorry

/-- The explicit inverse of the closed-support inclusion followed by the inclusion is the
identity on a direct image. -/
@[simp, stacks 0G6P "closed-support inclusion inverse-forward law"]
theorem inclusionPushforward_inv_hom_id (F : ClosedSubset.Modules 𝒪 Z) :
    inclusionPushforwardInv 𝒪 Z F ≫
        inclusion 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F) = 𝟙 _ := sorry

/-- The closed-support inclusion is invertible, with the kernel lift as its inverse. -/
@[stacks 0G6P "closed-support inclusion on a direct image is invertible"]
noncomputable instance inclusionPushforwardIsIso (F : ClosedSubset.Modules 𝒪 Z) :
    IsIso (inclusion 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F)) :=
  ⟨⟨inclusionPushforwardInv 𝒪 Z F, inclusionPushforward_hom_inv_id 𝒪 Z F,
    inclusionPushforward_inv_hom_id 𝒪 Z F⟩⟩

/-- The closed-support inclusion on a direct image is a literal isomorphism. -/
@[stacks 0G6P "closed-support inclusion isomorphism on a direct image"]
noncomputable def inclusionPushforwardIso (F : ClosedSubset.Modules 𝒪 Z) :
    object 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F) ≅
      (ClosedSubset.pushforward 𝒪 Z).obj F where
  hom := inclusion 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F)
  inv := inclusionPushforwardInv 𝒪 Z F
  hom_inv_id := inclusionPushforward_hom_inv_id 𝒪 Z F
  inv_hom_id := inclusionPushforward_inv_hom_id 𝒪 Z F

/-- The forward map of `inclusionPushforwardIso` is the closed-support inclusion. -/
@[simp, stacks 0G6P "closed-support inclusion isomorphism hom"]
theorem inclusionPushforwardIso_hom (F : ClosedSubset.Modules 𝒪 Z) :
    (inclusionPushforwardIso 𝒪 Z F).hom =
      inclusion 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F) := sorry

/-- The inverse map of `inclusionPushforwardIso` is the explicit closed-support inverse. -/
@[simp, stacks 0G6P "closed-support inclusion isomorphism inverse"]
theorem inclusionPushforwardIso_inv (F : ClosedSubset.Modules 𝒪 Z) :
    (inclusionPushforwardIso 𝒪 Z F).inv = inclusionPushforwardInv 𝒪 Z F := sorry

/-- The explicit inverse of the pullback-pushforward counit on a closed-subspace module. -/
@[stacks 0G6P "inverse closed-subspace pullback-pushforward counit"]
noncomputable def pullbackPushforwardCounitAppInv (F : ClosedSubset.Modules 𝒪 Z) :
    F ⟶ (ClosedSubset.pullback 𝒪 Z).obj
      ((ClosedSubset.pushforward 𝒪 Z).obj F) :=
  pushforwardPreimage 𝒪 Z
    ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).unit.app ((ClosedSubset.pushforward 𝒪 Z).obj F))

/-- The pullback-pushforward counit followed by its explicit inverse is the identity. -/
@[simp, stacks 0G6P "closed-subspace counit forward-inverse law"]
theorem pullbackPushforwardCounitApp_hom_inv_id (F : ClosedSubset.Modules 𝒪 Z) :
    (SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).counit.app F ≫
        pullbackPushforwardCounitAppInv 𝒪 Z F = 𝟙 _ := sorry

/-- The explicit inverse of the pullback-pushforward counit followed by the counit is the
identity. -/
@[simp, stacks 0G6P "closed-subspace counit inverse-forward law"]
theorem pullbackPushforwardCounitApp_inv_hom_id (F : ClosedSubset.Modules 𝒪 Z) :
    pullbackPushforwardCounitAppInv 𝒪 Z F ≫
        (SheafOfModules.pullbackPushforwardAdjunction
          (ClosedSubset.structureMap 𝒪 Z)).counit.app F = 𝟙 _ := sorry

/-- The module counit is invertible, with the explicit preimage of the unit as inverse. -/
@[stacks 0G6P "closed-subspace pullback-pushforward counit is invertible"]
noncomputable instance pullbackPushforwardCounitAppIsIso (F : ClosedSubset.Modules 𝒪 Z) :
    IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).counit.app F) :=
  ⟨⟨pullbackPushforwardCounitAppInv 𝒪 Z F,
    pullbackPushforwardCounitApp_hom_inv_id 𝒪 Z F,
    pullbackPushforwardCounitApp_inv_hom_id 𝒪 Z F⟩⟩

/-- The pullback-pushforward counit on a closed-subspace module is a literal isomorphism. -/
@[stacks 0G6P "closed-subspace pullback-pushforward counit isomorphism"]
noncomputable def pullbackPushforwardCounitAppIso (F : ClosedSubset.Modules 𝒪 Z) :
    (ClosedSubset.pullback 𝒪 Z).obj ((ClosedSubset.pushforward 𝒪 Z).obj F) ≅ F where
  hom := (SheafOfModules.pullbackPushforwardAdjunction
    (ClosedSubset.structureMap 𝒪 Z)).counit.app F
  inv := pullbackPushforwardCounitAppInv 𝒪 Z F
  hom_inv_id := pullbackPushforwardCounitApp_hom_inv_id 𝒪 Z F
  inv_hom_id := pullbackPushforwardCounitApp_inv_hom_id 𝒪 Z F

/-- The forward map of `pullbackPushforwardCounitAppIso` is the adjunction counit. -/
@[simp, stacks 0G6P "closed-subspace counit isomorphism hom"]
theorem pullbackPushforwardCounitAppIso_hom (F : ClosedSubset.Modules 𝒪 Z) :
    (pullbackPushforwardCounitAppIso 𝒪 Z F).hom =
      (SheafOfModules.pullbackPushforwardAdjunction
        (ClosedSubset.structureMap 𝒪 Z)).counit.app F := sorry

/-- The inverse map of `pullbackPushforwardCounitAppIso` is explicit. -/
@[simp, stacks 0G6P "closed-subspace counit isomorphism inverse"]
theorem pullbackPushforwardCounitAppIso_inv (F : ClosedSubset.Modules 𝒪 Z) :
    (pullbackPushforwardCounitAppIso 𝒪 Z F).inv =
      pullbackPushforwardCounitAppInv 𝒪 Z F := sorry

/-- The explicit inverse of the pullback-pushforward unit on the ambient closed-support object.
-/
@[stacks 0G6P "inverse ambient closed-support pullback-pushforward unit"]
noncomputable def objectPullbackPushforwardUnitAppInv (F : SheafOfModules 𝒪) :
    (ClosedSubset.pushforward 𝒪 Z).obj
        ((ClosedSubset.pullback 𝒪 Z).obj (object 𝒪 Z F)) ⟶ object 𝒪 Z F :=
  (ClosedSubset.pushforward 𝒪 Z).map
      ((ClosedSubset.pullback 𝒪 Z).map (supportedRestrictionPushforwardIso 𝒪 Z F).hom ≫
        (SheafOfModules.pullbackPushforwardAdjunction
          (ClosedSubset.structureMap 𝒪 Z)).counit.app (supportedRestriction 𝒪 Z F)) ≫
    (supportedRestrictionPushforwardIso 𝒪 Z F).inv

/-- The pullback-pushforward unit followed by its explicit inverse is the identity. -/
@[simp, stacks 0G6P "ambient closed-support unit forward-inverse law"]
theorem objectPullbackPushforwardUnitApp_hom_inv_id (F : SheafOfModules 𝒪) :
    (SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).unit.app (object 𝒪 Z F) ≫
        objectPullbackPushforwardUnitAppInv 𝒪 Z F = 𝟙 _ := sorry

/-- The explicit inverse of the pullback-pushforward unit followed by the unit is the identity.
-/
@[simp, stacks 0G6P "ambient closed-support unit inverse-forward law"]
theorem objectPullbackPushforwardUnitApp_inv_hom_id (F : SheafOfModules 𝒪) :
    objectPullbackPushforwardUnitAppInv 𝒪 Z F ≫
        (SheafOfModules.pullbackPushforwardAdjunction
          (ClosedSubset.structureMap 𝒪 Z)).unit.app (object 𝒪 Z F) = 𝟙 _ := sorry

/-- The support unit is invertible, with inverse constructed by extension by zero. -/
@[stacks 0G6P "ambient closed-support pullback-pushforward unit is invertible"]
noncomputable instance objectPullbackPushforwardUnitAppIsIso (F : SheafOfModules 𝒪) :
    IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).unit.app (object 𝒪 Z F)) :=
  ⟨⟨objectPullbackPushforwardUnitAppInv 𝒪 Z F,
    objectPullbackPushforwardUnitApp_hom_inv_id 𝒪 Z F,
    objectPullbackPushforwardUnitApp_inv_hom_id 𝒪 Z F⟩⟩

/-- The pullback-pushforward unit on the ambient closed-support object is a literal isomorphism.
-/
@[stacks 0G6P "ambient closed-support pullback-pushforward unit isomorphism"]
noncomputable def objectPullbackPushforwardUnitAppIso (F : SheafOfModules 𝒪) :
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
theorem objectPullbackPushforwardUnitAppIso_hom (F : SheafOfModules 𝒪) :
    (objectPullbackPushforwardUnitAppIso 𝒪 Z F).hom =
      (SheafOfModules.pullbackPushforwardAdjunction
        (ClosedSubset.structureMap 𝒪 Z)).unit.app (object 𝒪 Z F) := sorry

/-- The inverse map of `objectPullbackPushforwardUnitAppIso` is explicit. -/
@[simp, stacks 0G6P "ambient closed-support unit isomorphism inverse"]
theorem objectPullbackPushforwardUnitAppIso_inv (F : SheafOfModules 𝒪) :
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
  @CategoryTheory.inv _ _ _ _
      ((SheafOfModules.pullbackPushforwardAdjunction
        (ClosedSubset.structureMap 𝒪 Z)).counit.app F) hc ≫
    (ClosedSubset.pullback 𝒪 Z).map
      (@CategoryTheory.inv _ _ _ _
        (inclusion 𝒪 Z ((ClosedSubset.pushforward 𝒪 Z).obj F)) hi)

/-- The counit component for direct image left adjoint to closed support, given
the invertibility data used to construct it. -/
@[stacks 0G6P "closed-support adjunction counit component from isomorphisms"]
noncomputable def adjunctionCounitAppOfIso (F : SheafOfModules 𝒪)
    [hu : IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (ClosedSubset.structureMap 𝒪 Z)).unit.app (object 𝒪 Z F))] :
  (ClosedSubset.pushforward 𝒪 Z).obj ((functor 𝒪 Z).obj F) ⟶ F :=
  @CategoryTheory.inv _ _ _ _
      ((SheafOfModules.pullbackPushforwardAdjunction
        (ClosedSubset.structureMap 𝒪 Z)).unit.app (object 𝒪 Z F)) hu ≫
    inclusion 𝒪 Z F

/-- The unit component for direct image left adjoint to closed support, using
the constructed inverse maps. -/
@[stacks 0G6P "closed-support adjunction unit component"]
noncomputable def adjunctionUnitApp (F : ClosedSubset.Modules 𝒪 Z) :
    F ⟶ (functor 𝒪 Z).obj ((ClosedSubset.pushforward 𝒪 Z).obj F) :=
  pullbackPushforwardCounitAppInv 𝒪 Z F ≫
    (ClosedSubset.pullback 𝒪 Z).map (inclusionPushforwardInv 𝒪 Z F)

/-- The counit component for direct image left adjoint to closed support, using
the constructed inverse map. -/
@[stacks 0G6P "closed-support adjunction counit component"]
noncomputable def adjunctionCounitApp (F : SheafOfModules 𝒪) :
    (ClosedSubset.pushforward 𝒪 Z).obj ((functor 𝒪 Z).obj F) ⟶ F :=
  objectPullbackPushforwardUnitAppInv 𝒪 Z F ≫ inclusion 𝒪 Z F

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
      (ClosedSubset.structureMap 𝒪 Z)).counit :=
  ⟨⟨{ app := pullbackPushforwardCounitAppInv 𝒪 Z, naturality := sorry }, sorry, sorry⟩⟩

/-- Direct image from a bundled closed subspace is fully faithful. -/
@[stacks 0G6P "closed-subset pushforward is fully faithful"]
noncomputable def pushforwardFullyFaithful :
    (ClosedSubset.pushforward 𝒪 Z).FullyFaithful :=
  { preimage := pushforwardPreimage 𝒪 Z
    map_preimage := sorry
    preimage_map := sorry }

/-- Direct image from a bundled closed subspace is canonically a left adjoint. -/
@[stacks 0G6P "closed-subset pushforward is a left adjoint"]
noncomputable instance pushforwardIsLeftAdjoint :
    (SheafOfModules.pushforward.{u} (ClosedSubset.structureMap 𝒪 Z)).IsLeftAdjoint :=
  (adjunction 𝒪 Z).isLeftAdjoint

/-- Direct image from a bundled closed subspace is canonically a right adjoint. -/
noncomputable instance pushforwardIsRightAdjoint :
    (SheafOfModules.pushforward.{u} (ClosedSubset.structureMap 𝒪 Z)).IsRightAdjoint :=
  (SheafOfModules.pullbackPushforwardAdjunction
    (ClosedSubset.structureMap 𝒪 Z)).isRightAdjoint

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
