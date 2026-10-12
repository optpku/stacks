/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import stacks_project.Chap59.Definition_59_70_1_ExtensionByZero
public import stacks_project.Chap63.Definition_63_3_7_CompactSupport
public import stacks_project.Chap63.Remark_63_3_5_Covariance_with_respect_to_open_embeddings_OpenImmersion

/-!
# Covariance of compactly supported global étale sections along open immersions

For a separated scheme `X` locally of finite type over a field `k` and an abelian
étale sheaf `F`, an open immersion `j : X' ⟶ X` over `k` induces an injective
additive map `H^0_c(X', F|_{X'}) →+ H^0_c(X, F)` by unique extension of properly
supported sections as in `extendSupportedAlongOpen`. These maps assemble into a
covariant functor on Zariski opens of `X`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {k : Type u} [Field k]

/-- The additive subgroup `H^0_c(X, F)` of global étale sections with compact
support. -/
def globalSectionsCompactSupportSubgroup (X : SchemeOverField k)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    AddSubgroup (F.obj.obj (op (globalEtale X.left))) where
  carrier := globalSectionsCompactSupport F
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- Membership in the compactly supported global-section subgroup is compact
support of the section. -/
theorem mem_globalSectionsCompactSupportSubgroup_iff (X : SchemeOverField k)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : F.obj.obj (op (globalEtale X.left))) :
    σ ∈ globalSectionsCompactSupportSubgroup X F ↔ HasCompactSupport F σ :=
  sorry

/-- The morphism of small étale identity objects `X'_étale ⟶ X_étale` induced by
an open immersion over `k`. -/
def globalEtaleOpenImmersion {X X' : SchemeOverField k} (j : X' ⟶ X)
    [IsOpenImmersion j.left] :
    (etaleRestriction j.left).obj (globalEtale X'.left) ⟶ globalEtale X.left :=
  MorphismProperty.Over.homMk j.left

/-- The reduced closed-subscheme structure on the support of a compactly
supported global section of `F|_{X'}`. -/
def globalCompactSupportSectionStructure {X X' : SchemeOverField k}
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)) :
    ClosedSubschemeStructure
      (abelianSheafSectionSupport
        ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)
        (globalEtale X'.left)
        ((globalSectionsCompactSupportSubgroup X'
            ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)).subtype σ)) :=
  ClosedSubschemeStructure.reduced _

/-- The reduced support of a compactly supported global section is a closed
immersion into `X'`. -/
instance isClosedImmersion_globalCompactSupportSectionStructure_ι
    {X X' : SchemeOverField k} [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom]
    (j : X' ⟶ X) [IsOpenImmersion j.left]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)) :
    IsClosedImmersion (globalCompactSupportSectionStructure j F σ).ι :=
  inferInstanceAs
    (IsClosedImmersion (globalCompactSupportSectionStructure j F σ).ideal.subschemeι)

/-- The support of a compactly supported global section of `F|_{X'}` remains a
closed immersion after composing with `j.left`. -/
theorem isClosedImmersion_support_globalOpenImmersion {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)) :
    IsClosedImmersion
      ((globalCompactSupportSectionStructure j F σ).ι ≫
        (globalEtaleOpenImmersion j).left) :=
  sorry

/-- A compactly supported global section of `F|_{X'}` is supported in the image
of its reduced support subscheme, as a section of `F` on the image of `X'` in
`X.Etale`. -/
theorem globalCompactSupportSections_mem_supportedIn {X X' : SchemeOverField k}
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)) :
    ((globalSectionsCompactSupportSubgroup X'
          ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)).subtype σ) ∈
      abelianSheafSectionsSupportedIn F
        ((etaleRestriction j.left).obj (globalEtale X'.left))
        (Set.range (globalCompactSupportSectionStructure j F σ).ι) :=
  sorry

/-- The unique extension of a compactly supported global section of `F|_{X'}` to
a global section of `F` on `X`, via `extendSupportedAlongOpen`. -/
def extendGlobalCompactSupportSection {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)) :
    F.obj.obj (op (globalEtale X.left)) :=
  (@extendSupportedAlongOpen _ F _ _ (globalEtaleOpenImmersion j) _
      (globalCompactSupportSectionStructure j F σ).ι
      (isClosedImmersion_globalCompactSupportSectionStructure_ι j F σ)
      (isClosedImmersion_support_globalOpenImmersion j F σ)
      ⟨(globalSectionsCompactSupportSubgroup X'
            ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)).subtype σ,
        globalCompactSupportSections_mem_supportedIn j F σ⟩).val

/-- The unique extension of a compactly supported global section along an open
immersion still has compact support. -/
theorem hasCompactSupport_extendGlobalCompactSupportSection {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)) :
    HasCompactSupport F (extendGlobalCompactSupportSection j F σ) :=
  sorry

/-- Canonical covariance `H^0_c(X', F|_{X'}) →+ H^0_c(X, F)` along an open
immersion of separated locally finite-type `k`-schemes. -/
def globalSectionsCompactSupportOpenImmersion {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    globalSectionsCompactSupportSubgroup X'
        ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F) →+
      globalSectionsCompactSupportSubgroup X F where
  toFun σ :=
    ⟨extendGlobalCompactSupportSection j F σ,
      (mem_globalSectionsCompactSupportSubgroup_iff X F
          (extendGlobalCompactSupportSection j F σ)).mpr
        (hasCompactSupport_extendGlobalCompactSupportSection j F σ)⟩
  map_zero' := sorry
  map_add' := sorry

/-- The covariance map acts by unique extension of properly supported sections. -/
theorem globalSectionsCompactSupportOpenImmersion_apply {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)) :
    (globalSectionsCompactSupportOpenImmersion j F σ).val =
      extendGlobalCompactSupportSection j F σ :=
  sorry

/-- The covariance map `H^0_c(X', F|_{X'}) ⟶ H^0_c(X, F)` is injective. -/
theorem globalSectionsCompactSupportOpenImmersion_injective {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Injective (globalSectionsCompactSupportOpenImmersion j F) :=
  sorry

/-- Restriction of the extended global section along the open immersion recovers
the original compactly supported section. -/
theorem globalSectionsCompactSupportOpenImmersion_restrict {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)) :
    F.obj.map (globalEtaleOpenImmersion j).op
        (extendGlobalCompactSupportSection j F σ) =
      (globalSectionsCompactSupportSubgroup X'
          ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)).subtype σ :=
  sorry

/-- Covariance along the identity open immersion is the identity. -/
theorem globalSectionsCompactSupportOpenImmersion_id (X : SchemeOverField k)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    globalSectionsCompactSupportOpenImmersion (𝟙 X) F =
      AddMonoidHom.id (globalSectionsCompactSupportSubgroup X F) :=
  sorry

/-- Restriction of abelian small-étale sheaves along equal étale morphisms is
isomorphic. -/
def etaleRestrictionSheafCongr {U X : Scheme.{u}} {f g : U ⟶ X}
    [Etale f] [Etale g] (e : f = g) :
    etaleRestrictionSheaf f AddCommGrpCat.{u} ≅
      etaleRestrictionSheaf g AddCommGrpCat.{u} :=
  eqToIso (e ▸ rfl)

/-- Site-level identification of étale restriction along a composite open
immersion with the composite of the restrictions. -/
def etaleRestriction_comp_open {X X' X'' : Scheme.{u}} (j : X' ⟶ X) (j' : X'' ⟶ X')
    [IsOpenImmersion j] [IsOpenImmersion j'] :
    etaleRestriction (j' ≫ j) ≅ etaleRestriction j' ⋙ etaleRestriction j :=
  MorphismProperty.Over.mapComp (P := @Etale) (Q := (⊤ : MorphismProperty Scheme))
    (inferInstance : Etale j') (inferInstance : Etale j) (j' ≫ j) rfl

/-- Sheaf-level identification of restriction along a composite open immersion
with the composite of the restrictions. -/
def etaleRestrictionSheaf_comp_open {X X' X'' : Scheme.{u}}
    (j : X' ⟶ X) (j' : X'' ⟶ X') [IsOpenImmersion j] [IsOpenImmersion j'] :
    etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙
        etaleRestrictionSheaf j' AddCommGrpCat.{u} ≅
      etaleRestrictionSheaf (j' ≫ j) AddCommGrpCat.{u} :=
  sheafPushforwardContinuousComp' (etaleRestriction_comp_open j j').symm
    AddCommGrpCat.{u} X''.smallEtaleTopology X'.smallEtaleTopology
    X.smallEtaleTopology

/-- A sheaf isomorphism preserves compact support of global étale sections. -/
theorem mem_globalSectionsCompactSupportSubgroup_mapIso (X : SchemeOverField k)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    {F G : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}} (α : F ≅ G)
    (σ : globalSectionsCompactSupportSubgroup X F) :
    (α.hom.hom.app (op (globalEtale X.left)))
        ((globalSectionsCompactSupportSubgroup X F).subtype σ) ∈
      globalSectionsCompactSupportSubgroup X G :=
  sorry

/-- The map on compactly supported global sections induced by an isomorphism of
abelian étale sheaves. -/
def globalSectionsCompactSupportMapIso (X : SchemeOverField k)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    {F G : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}} (α : F ≅ G) :
    globalSectionsCompactSupportSubgroup X F →+
      globalSectionsCompactSupportSubgroup X G :=
  (((α.hom.hom.app (op (globalEtale X.left))).hom.comp
        (globalSectionsCompactSupportSubgroup X F).subtype).codRestrict
    (globalSectionsCompactSupportSubgroup X G)
    (mem_globalSectionsCompactSupportSubgroup_mapIso X α))

/-- The underlying scheme morphism of a composite open immersion over `k` is an
open immersion. -/
instance isOpenImmersion_comp_over_left {X X' X'' : SchemeOverField k}
    (j : X' ⟶ X) (j' : X'' ⟶ X')
    [IsOpenImmersion j.left] [IsOpenImmersion j'.left] :
    IsOpenImmersion (j' ≫ j).left :=
  inferInstanceAs (IsOpenImmersion (j'.left ≫ j.left))

/-- Covariance along nested open immersions `X'' ⟶ X' ⟶ X` is the composite of
the two covariance maps, after identifying the two-step restriction of `F` with
restriction along the composite. -/
theorem globalSectionsCompactSupportOpenImmersion_comp {X X' X'' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom]
    [IsSeparated X''.hom] [LocallyOfFiniteType X''.hom]
    (j : X' ⟶ X) (j' : X'' ⟶ X') [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    (globalSectionsCompactSupportOpenImmersion j F).comp
        ((globalSectionsCompactSupportOpenImmersion j'
            ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)).comp
          (globalSectionsCompactSupportMapIso X''
            ((etaleRestrictionSheaf_comp_open j.left j'.left).symm.app F))) =
      globalSectionsCompactSupportOpenImmersion (j' ≫ j) F :=
  sorry

/-- The open subscheme `U ⊆ X` as a scheme over the same field. -/
def restrictOpenOverField (X : SchemeOverField k) (U : X.left.Opens) :
    SchemeOverField k :=
  Over.mk (U.ι ≫ X.hom)

/-- An open subscheme of a separated `k`-scheme remains separated over `k`. -/
instance isSeparated_restrictOpenOverField_hom (X : SchemeOverField k)
    [IsSeparated X.hom] (U : X.left.Opens) :
    IsSeparated (restrictOpenOverField X U).hom :=
  inferInstanceAs (IsSeparated (U.ι ≫ X.hom))

/-- An open subscheme of a locally finite-type `k`-scheme remains locally of
finite type over `k`. -/
instance locallyOfFiniteType_restrictOpenOverField_hom (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (U : X.left.Opens) :
    LocallyOfFiniteType (restrictOpenOverField X U).hom :=
  inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))

/-- An inclusion of Zariski opens induces a morphism of `k`-schemes. -/
def restrictOpenOverFieldHom (X : SchemeOverField k) {U V : X.left.Opens}
    (h : U ≤ V) : restrictOpenOverField X U ⟶ restrictOpenOverField X V :=
  Over.homMk (X.left.homOfLE h) (X.left.homOfLE_ι_assoc h X.hom)

/-- The underlying scheme morphism of `restrictOpenOverFieldHom` is an open
immersion. -/
instance isOpenImmersion_restrictOpenOverFieldHom_left (X : SchemeOverField k)
    {U V : X.left.Opens} (h : U ≤ V) :
    IsOpenImmersion (restrictOpenOverFieldHom X h).left :=
  inferInstanceAs (IsOpenImmersion (X.left.homOfLE h))

/-- The open immersion of a Zariski open `U ⊆ X` as a morphism of `k`-schemes. -/
def restrictOpenOverFieldι (X : SchemeOverField k) (U : X.left.Opens) :
    restrictOpenOverField X U ⟶ X :=
  Over.homMk U.ι

/-- The underlying scheme morphism of `restrictOpenOverFieldι` is an open
immersion. -/
instance isOpenImmersion_restrictOpenOverFieldι_left (X : SchemeOverField k)
    (U : X.left.Opens) :
    IsOpenImmersion (restrictOpenOverFieldι X U).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

/-- Restriction of `F` to `U` identifies with restriction to `V` followed by
restriction along `X.homOfLE h`. -/
def etaleRestrictionSheaf_opensLe {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {U V : X.Opens} (h : U ≤ V) :
    (etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj F ≅
      (etaleRestrictionSheaf (X.homOfLE h) AddCommGrpCat.{u}).obj
        ((etaleRestrictionSheaf V.ι AddCommGrpCat.{u}).obj F) :=
  (etaleRestrictionSheafCongr (X.homOfLE_ι h).symm).app F ≪≫
    (etaleRestrictionSheaf_comp_open V.ι (X.homOfLE h)).symm.app F

/-- Covariance of compactly supported global sections along an inclusion of
Zariski opens of `X`. -/
def globalSectionsCompactSupportOpensHom {X : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) {U V : X.left.Opens}
    (h : U ≤ V) :
    globalSectionsCompactSupportSubgroup (restrictOpenOverField X U)
        ((etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj F) →+
      globalSectionsCompactSupportSubgroup (restrictOpenOverField X V)
        ((etaleRestrictionSheaf V.ι AddCommGrpCat.{u}).obj F) :=
  (globalSectionsCompactSupportOpenImmersion (restrictOpenOverFieldHom X h)
      ((etaleRestrictionSheaf V.ι AddCommGrpCat.{u}).obj F)).comp
    (globalSectionsCompactSupportMapIso (restrictOpenOverField X U)
      (etaleRestrictionSheaf_opensLe F h))

/-- Covariance of compactly supported global sections along the open immersion of
a Zariski open subscheme of `X`. -/
abbrev globalSectionsCompactSupportOpens {X : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (U : X.left.Opens) :
    globalSectionsCompactSupportSubgroup (restrictOpenOverField X U)
        ((etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj F) →+
      globalSectionsCompactSupportSubgroup X F :=
  globalSectionsCompactSupportOpenImmersion (restrictOpenOverFieldι X U) F

/-- The assignment `U ↦ H^0_c(U, F|_U)` on Zariski opens of `X`, with covariance
maps along open inclusions. This is the quoted “cosheaf” of compactly supported
global sections, packaged as a covariant functor rather than a codescent axiom. -/
def globalSectionsCompactSupportCopresheaf {X : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    X.left.Opens ⥤ AddCommGrpCat.{u} where
  obj U :=
    AddCommGrpCat.of
      (globalSectionsCompactSupportSubgroup (restrictOpenOverField X U)
        ((etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj F))
  map {U V} h :=
    AddCommGrpCat.ofHom (globalSectionsCompactSupportOpensHom F (leOfHom h))
  map_id := sorry
  map_comp := sorry

end AlgebraicGeometry.Scheme.Etale

end
