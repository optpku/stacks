/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import stacks_project.Chap63.«63_4_0_2_LowerShriekPresheaf»
public import stacks_project.Chap63.Lemma_63_3_4_LowerShriek

/-!
# Finite-support comparison for compact-support étale lower shriek

Canonical maps identifying the colimit presheaf `f_{p!}` with the underlying
presheaf of the compact-support sheaf `f_!`, together with the finite-support
section API used to describe the values.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

open FiniteSupport

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A section of `F` on the small-étale pullback `X_V` has finite support over
`V` when the reduced induced closed subscheme of its étale section support is
finite over `V`. -/
def HasFiniteSupport (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) : Prop :=
  IsFinite
    ((Scheme.ClosedSubschemeStructure.reduced
        (abelianSheafSectionSupport F ((smallEtalePullback f).obj V) σ)).ι ≫
      pullback.fst V.hom f)

/-- Finite support of a section is finiteness of its reduced étale section
support over the base. -/
theorem hasFiniteSupport_iff (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) :
    HasFiniteSupport f F V σ ↔
      IsFinite
        ((Scheme.ClosedSubschemeStructure.reduced
            (abelianSheafSectionSupport F ((smallEtalePullback f).obj V) σ)).ι ≫
          pullback.fst V.hom f) :=
  sorry

/-- The additive subgroup of sections of `F` on `X_V` whose support is finite
over `V`. -/
def finiteSupportSections (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) :
    AddSubgroup (F.obj.obj (op ((smallEtalePullback f).obj V))) where
  carrier := {σ | HasFiniteSupport f F V σ}
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- Membership in the finite-support subgroup is the finite-support
predicate. -/
theorem mem_finiteSupportSections_iff
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) :
    σ ∈ finiteSupportSections f F V ↔ HasFiniteSupport f F V σ :=
  sorry

variable [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f]

/-- Under a separated locally quasi-finite morphism, a section has finite
support over `V` if and only if it has proper support over `V`. -/
theorem hasFiniteSupport_iff_hasProperSupport
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) :
    HasFiniteSupport f F V σ ↔ HasProperSupport f F V σ :=
  sorry

/-- Under a separated locally quasi-finite morphism, finite-support sections
coincide with compactly supported sections. -/
theorem finiteSupportSections_eq_compactSupportSections
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    finiteSupportSections f F V = compactSupportSections f F V :=
  sorry

/-- An admissible locally closed support that is finite over `V` is closed in
`X_V`, because `f` is separated. -/
theorem isClosed_subset {V : Y.Etale} (A : Admissible f V) :
    IsClosed (A.subset : Set (baseChangeScheme f V)) :=
  sorry

/-- The étale `X`-scheme cut out by the ambient open of an admissible
support. -/
def ambientEtale {V : Y.Etale} (A : Admissible f V) : X.Etale :=
  mk (A.ambient.ι ≫ baseChangeToSource f V)

/-- The structure morphism of `ambientEtale` is the ambient open inclusion
followed by `X_V ⟶ X`. -/
theorem ambientEtale_hom {V : Y.Etale} (A : Admissible f V) :
    (ambientEtale f A).hom = A.ambient.ι ≫ baseChangeToSource f V :=
  sorry

/-- The open complement of an admissible support in `X_V`. -/
def complementOpen {V : Y.Etale} (A : Admissible f V) :
    (baseChangeScheme f V).Opens :=
  ⟨(A.subset : Set (baseChangeScheme f V))ᶜ,
    (isClosed_subset f A).isOpen_compl⟩

/-- The underlying set of `complementOpen` is the set-theoretic complement of
the admissible support. -/
theorem coe_complementOpen {V : Y.Etale} (A : Admissible f V) :
    (complementOpen f A : Set (baseChangeScheme f V)) =
      (A.subset : Set (baseChangeScheme f V))ᶜ :=
  sorry

/-- The étale `X`-scheme cut out by the complement of an admissible support. -/
def complementEtale {V : Y.Etale} (A : Admissible f V) : X.Etale :=
  mk ((complementOpen f A).ι ≫ baseChangeToSource f V)

/-- The structure morphism of `complementEtale` is the complement inclusion
followed by `X_V ⟶ X`. -/
theorem complementEtale_hom {V : Y.Etale} (A : Admissible f V) :
    (complementEtale f A).hom =
      (complementOpen f A).ι ≫ baseChangeToSource f V :=
  sorry

/-- The inclusion of the ambient étale object into the base change `X_V`. -/
def ambientInclusion {V : Y.Etale} (A : Admissible f V) :
    ambientEtale f A ⟶ (smallEtalePullback f).obj V :=
  MorphismProperty.Over.homMk A.ambient.ι sorry

/-- The underlying scheme morphism of `ambientInclusion` is the ambient open
inclusion. -/
theorem ambientInclusion_left {V : Y.Etale} (A : Admissible f V) :
    (ambientInclusion f A).left = A.ambient.ι :=
  sorry

/-- The inclusion of the complementary étale object into the base change
`X_V`. -/
def complementInclusion {V : Y.Etale} (A : Admissible f V) :
    complementEtale f A ⟶ (smallEtalePullback f).obj V :=
  MorphismProperty.Over.homMk (complementOpen f A).ι sorry

/-- The underlying scheme morphism of `complementInclusion` is the complement
open inclusion. -/
theorem complementInclusion_left {V : Y.Etale} (A : Admissible f V) :
    (complementInclusion f A).left = (complementOpen f A).ι :=
  sorry

/-- The two members of the Zariski cover of `X_V` by the ambient open and the
complement of `Z`. -/
def supportCoverObject {V : Y.Etale} (A : Admissible f V) : Bool → X.Etale
  | false => ambientEtale f A
  | true => complementEtale f A

/-- The two inclusions in the Zariski cover of `X_V` by the ambient open and the
complement of `Z`. -/
def supportCoverMap {V : Y.Etale} (A : Admissible f V) :
    ∀ i : Bool, supportCoverObject f A i ⟶ (smallEtalePullback f).obj V
  | false => ambientInclusion f A
  | true => complementInclusion f A

/-- Evaluating `supportCoverMap` recovers the ambient and complementary
inclusions. -/
theorem supportCoverMap_apply {V : Y.Etale} (A : Admissible f V) :
    supportCoverMap f A false = ambientInclusion f A ∧
      supportCoverMap f A true = complementInclusion f A :=
  sorry

/-- Evaluating `supportCoverObject` recovers the ambient and complementary étale
objects. -/
theorem supportCoverObject_apply {V : Y.Etale} (A : Admissible f V) :
    supportCoverObject f A false = ambientEtale f A ∧
      supportCoverObject f A true = complementEtale f A :=
  sorry

/-- The ambient open and the complement of `Z` cover `X_V` in the small étale
topology. -/
theorem supportCover_mem {V : Y.Etale} (A : Admissible f V) :
    Sieve.ofArrows (supportCoverObject f A) (supportCoverMap f A) ∈
      X.smallEtaleTopology ((smallEtalePullback f).obj V) :=
  sorry

/-- On the ambient member use the supported section; on the complement use
zero. -/
def supportExtensionLocalMap (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V : Y.Etale} (A : Admissible f V) :
    ∀ i : Bool,
      sections f F A ⟶ F.obj.obj (op (supportCoverObject f A i))
  | false =>
    AddCommGrpCat.ofHom
      (sectionsSupportedIn F (baseChangeToSource f V) A.subset A.ambient
        A.subset_le_ambient A.isClosed_in_ambient).subtype
  | true => 0

/-- The complementary local map in the zero-extension cover is the zero
morphism. -/
theorem supportExtensionLocalMap_true
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V : Y.Etale}
    (A : Admissible f V) :
    supportExtensionLocalMap f F A true = 0 :=
  sorry

/-- The supported section on the ambient open and zero on the complement agree
on every overlap. -/
theorem supportExtensionLocalMap_compatible
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V : Y.Etale}
    (A : Admissible f V) :
    ∀ (W : X.Etale) (i k : Bool) (a : W ⟶ supportCoverObject f A i)
      (b : W ⟶ supportCoverObject f A k),
      a ≫ supportCoverMap f A i = b ≫ supportCoverMap f A k →
        supportExtensionLocalMap f F A i ≫ F.obj.map a.op =
          supportExtensionLocalMap f F A k ≫ F.obj.map b.op :=
  sorry

/-- Extend a section supported in an admissible `Z` by zero along the cover
`U ∪ (X_V \ Z)`. -/
def supportExtensionByZero (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V : Y.Etale} (A : Admissible f V) :
    sections f F A ⟶ F.obj.obj (op ((smallEtalePullback f).obj V)) :=
  F.property.amalgamateOfArrows (supportCoverMap f A) (supportCover_mem f A)
    (supportExtensionLocalMap f F A)
    (fun {W i k} a b h ↦
      supportExtensionLocalMap_compatible f F A W i k a b h)

/-- Extension by zero of an admissible supported section lands in the
compact-support subgroup. -/
theorem supportExtensionByZero_mem_compactSupportSections
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V : Y.Etale}
    (A : Admissible f V) (σ : sections f F A) :
    (supportExtensionByZero f F A).hom σ ∈ compactSupportSections f F V :=
  sorry

/-- The objectwise comparison `H_Z(F) ⟶ f_! F(V)` obtained by extending a
supported section by zero. -/
def sectionsToCompactSupport (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V : Y.Etale} (A : Admissible f V) :
    sections f F A ⟶ AddCommGrpCat.of (compactSupportSections f F V) :=
  AddCommGrpCat.ofHom
    ((supportExtensionByZero f F A).hom.codRestrict
      (compactSupportSections f F V)
      (supportExtensionByZero_mem_compactSupportSections f F A))

/-- The zero-extension comparison acts by the amalgamation of the supported
section with zero. -/
theorem sectionsToCompactSupport_apply
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V : Y.Etale}
    (A : Admissible f V) (σ : sections f F A) :
    (sectionsToCompactSupport f F A).hom σ =
      ⟨(supportExtensionByZero f F A).hom σ,
        supportExtensionByZero_mem_compactSupportSections f F A σ⟩ :=
  sorry

/-- Cocone of zero-extension maps from the finite-support diagram on `X_V`. -/
def sectionsToCompactSupportCocone
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    Cocone (diagram f F V) :=
  Cocone.mk (AddCommGrpCat.of (compactSupportSections f F V))
    { app := fun A ↦ sectionsToCompactSupport f F A
      naturality := sorry }

/-- The vertex of the zero-extension cocone is the group of compactly supported
sections. -/
theorem sectionsToCompactSupportCocone_pt
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    (sectionsToCompactSupportCocone f F V).pt =
      AddCommGrpCat.of (compactSupportSections f F V) :=
  sorry

/-- The canonical comparison `f_{p!} F(V) ⟶ f_! F(V)` obtained by descending
zero-extension maps out of the colimit of `H_Z(F)`. -/
def lowerShriekPresheafComparisonApp
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    ((lowerShriekPresheaf f).obj F).obj (op V) ⟶
      AddCommGrpCat.of (compactSupportSections f F V) :=
  colimit.desc (diagram f F V) (sectionsToCompactSupportCocone f F V)

/-- The objectwise comparison is the colimit descent of zero-extension maps. -/
theorem lowerShriekPresheafComparisonApp_eq
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    lowerShriekPresheafComparisonApp f F V =
      colimit.desc (diagram f F V) (sectionsToCompactSupportCocone f F V) :=
  sorry

/-- The canonical forward comparison `f_{p!} ⟶ f_!` of abelian presheaves on
`Y_étale`. -/
def lowerShriekPresheafComparison :
    lowerShriekPresheaf f ⟶
      etaleLowerShriek f ⋙
        sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u} where
  app F :=
    { app := fun V ↦ lowerShriekPresheafComparisonApp f F V.unop
      naturality := sorry }
  naturality := sorry

/-- Evaluating the forward comparison at an abelian étale sheaf and an étale
`Y`-scheme. -/
theorem lowerShriekPresheafComparison_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    ((lowerShriekPresheafComparison f).app F).app (op V) =
      lowerShriekPresheafComparisonApp f F V :=
  sorry

/-- The top open of `X_V` as an étale `X`-scheme is canonically the small-étale
pullback object `(smallEtalePullback f).obj V`. -/
def topOpenEtaleIso (V : Y.Etale) :
    mk ((⊤ : (baseChangeScheme f V).Opens).ι ≫ baseChangeToSource f V) ≅
      (smallEtalePullback f).obj V :=
  MorphismProperty.Over.isoMk (Scheme.topIso (baseChangeScheme f V)) sorry

/-- The underlying scheme isomorphism of `topOpenEtaleIso` is `Scheme.topIso`. -/
theorem topOpenEtaleIso_hom_left (V : Y.Etale) :
    (topOpenEtaleIso f V).hom.left = (Scheme.topIso (baseChangeScheme f V)).hom :=
  sorry

/-- The locally closed subset of `X_V` underlying the closed étale support of a
section. -/
def sectionSupportLocallyClosed
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) :
    LocallyCloseds (baseChangeScheme f V) :=
  ⟨(abelianSheafSectionSupport F ((smallEtalePullback f).obj V) σ :
      Set (baseChangeScheme f V)),
    (abelianSheafSectionSupport F ((smallEtalePullback f).obj V) σ).isClosed.isLocallyClosed⟩

/-- The locally closed subset recorded by `sectionSupportLocallyClosed` is the
étale section support. -/
theorem sectionSupportLocallyClosed_coe
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) :
    (sectionSupportLocallyClosed f F V σ : Set (baseChangeScheme f V)) =
      abelianSheafSectionSupport F ((smallEtalePullback f).obj V) σ :=
  sorry

/-- The admissible support on `X_V` with ambient open `⊤` associated to the
closed étale support of a compactly supported section. -/
def finiteSupportAdmissible (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) (σ : compactSupportSections f F V) :
    Admissible f V where
  subset := sectionSupportLocallyClosed f F V σ.1
  ambient := ⊤
  subset_le_ambient := Set.subset_univ _
  isClosed_in_ambient := sorry
  toBase_isFinite := sorry

/-- The admissible support of a compactly supported section records its étale
section support with ambient open `⊤`. -/
theorem finiteSupportAdmissible_subset
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections f F V) :
    (finiteSupportAdmissible f F V σ).subset =
      sectionSupportLocallyClosed f F V σ.1 ∧
      (finiteSupportAdmissible f F V σ).ambient = ⊤ :=
  sorry

/-- The transported section on the top open lies in `H_Z(F)` for the admissible
support of `σ`. -/
theorem topOpen_mem_sectionsSupportedIn
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections f F V) :
    (F.obj.map (topOpenEtaleIso f V).hom.op).hom σ.1 ∈
      sectionsSupportedIn F (baseChangeToSource f V)
        (finiteSupportAdmissible f F V σ).subset
        (finiteSupportAdmissible f F V σ).ambient
        (finiteSupportAdmissible f F V σ).subset_le_ambient
        (finiteSupportAdmissible f F V σ).isClosed_in_ambient :=
  sorry

/-- The objectwise inverse comparison `f_! F(V) ⟶ f_{p!} F(V)` sending a
compactly supported section to its class in the colimit of `H_Z(F)`. -/
def lowerShriekPresheafComparisonInvApp
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    AddCommGrpCat.of (compactSupportSections f F V) ⟶
      ((lowerShriekPresheaf f).obj F).obj (op V) :=
  AddCommGrpCat.ofHom
    { toFun := fun σ ↦
        (colimit.ι (diagram f F V) (finiteSupportAdmissible f F V σ)).hom
          ⟨(F.obj.map (topOpenEtaleIso f V).hom.op).hom σ.1,
            topOpen_mem_sectionsSupportedIn f F V σ⟩
      map_zero' := sorry
      map_add' := sorry }

/-- The objectwise inverse comparison is the indicated colimit coprojection. -/
theorem lowerShriekPresheafComparisonInvApp_apply
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections f F V) :
    (lowerShriekPresheafComparisonInvApp f F V).hom σ =
      (colimit.ι (diagram f F V) (finiteSupportAdmissible f F V σ)).hom
        ⟨(F.obj.map (topOpenEtaleIso f V).hom.op).hom σ.1,
          topOpen_mem_sectionsSupportedIn f F V σ⟩ :=
  sorry

/-- The canonical inverse comparison `f_! ⟶ f_{p!}` of abelian presheaves on
`Y_étale`. -/
def lowerShriekPresheafComparisonInv :
    etaleLowerShriek f ⋙
        sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⟶
      lowerShriekPresheaf f where
  app F :=
    { app := fun V ↦ lowerShriekPresheafComparisonInvApp f F V.unop
      naturality := sorry }
  naturality := sorry

/-- Evaluating the inverse comparison at an abelian étale sheaf and an étale
`Y`-scheme. -/
theorem lowerShriekPresheafComparisonInv_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    ((lowerShriekPresheafComparisonInv f).app F).app (op V) =
      lowerShriekPresheafComparisonInvApp f F V :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
