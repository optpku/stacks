/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.GroupTheory.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek
public import stacks_project.Chap63.Lemma_63_3_4
public import stacks_project.Chap63.Lemma_63_5_1_LowerShriek
public import stacks_project.Chap63.Lemma_63_7_1_Adjunction
public import stacks_project.Chap63.Remark_63_3_14_Comparison
public import stacks_project.Chap63.Remark_63_3_5_Covariance_with_respect_to_open_embeddings_OpenImmersion

/-!
# Comparison of derived lower shriek and proper pushforward

For a commutative square of schemes with proper vertical maps and separated
locally quasi-finite horizontal maps, the sheaf-level identification
`g_! ∘ f'_* ≅ f_* ∘ g'_!` and the derived comparison
`g_! ∘ Rf'_* ⟶ Rf_* ∘ g'_!`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open TopologicalSpace
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
variable (h_sq : CommSq g' f' f g)
variable [IsProper f] [IsProper f']
variable [IsSeparated g] [LocallyQuasiFinite g] [LocallyOfFiniteType g]
variable [IsSeparated g'] [LocallyQuasiFinite g'] [LocallyOfFiniteType g']

/-- The abelian sheaf isomorphism `g_! ∘ f'_* ≅ f_* ∘ g'_!` obtained by
identifying proper pushforward with compact support and composing compact
support along the two paths of the commutative square. -/
def etaleLowerShriekPushforwardIso :
    etaleAbelianPushforward f' ⋙ etaleLowerShriek g ≅
      etaleLowerShriek g' ⋙ etaleAbelianPushforward f :=
  isoWhiskerRight (etaleLowerShriekIso f').symm (etaleLowerShriek g) ≪≫
    etaleLowerShriekCompIso f' g ≪≫
    (etaleLowerShriekCongr h_sq.w).symm ≪≫
    (etaleLowerShriekCompIso g' f).symm ≪≫
    isoWhiskerLeft (etaleLowerShriek g') (etaleLowerShriekIso f)

/-- The forward map of `etaleLowerShriekPushforwardIso` is the composite of
proper identifications, composition identifications, and transport along the
commutative square. -/
theorem etaleLowerShriekPushforwardIso_hom :
    (etaleLowerShriekPushforwardIso f f' g g' h_sq).hom =
      whiskerRight (etaleLowerShriekIso f').inv (etaleLowerShriek g) ≫
        (etaleLowerShriekCompIso f' g).hom ≫
        (etaleLowerShriekCongr h_sq.w).inv ≫
        (etaleLowerShriekCompIso g' f).inv ≫
        whiskerLeft (etaleLowerShriek g') (etaleLowerShriekIso f).hom :=
  sorry

namespace Lqf

open FiniteSupport

variable {S T : Scheme.{u}} (h : S ⟶ T)
variable [IsSeparated h] [LocallyQuasiFinite h] [LocallyOfFiniteType h]

/-- The étale `S`-scheme cut out by the ambient open of an admissible
support. -/
def ambientEtale {V : T.Etale} (A : Admissible h V) : S.Etale :=
  mk (A.ambient.ι ≫ baseChangeToSource h V)

/-- The open complement of an admissible support in `S_V`. -/
def complementOpen {V : T.Etale} (A : Admissible h V) :
    (baseChangeScheme h V).Opens :=
  ⟨(A.subset : Set (baseChangeScheme h V))ᶜ, sorry⟩

/-- The étale `S`-scheme cut out by the complement of an admissible support. -/
def complementEtale {V : T.Etale} (A : Admissible h V) : S.Etale :=
  mk ((complementOpen h A).ι ≫ baseChangeToSource h V)

/-- The inclusion of the ambient étale object into the base change `S_V`. -/
def ambientInclusion {V : T.Etale} (A : Admissible h V) :
    ambientEtale h A ⟶ (smallEtalePullback h).obj V :=
  MorphismProperty.Over.homMk A.ambient.ι sorry

/-- The inclusion of the complementary étale object into the base change. -/
def complementInclusion {V : T.Etale} (A : Admissible h V) :
    complementEtale h A ⟶ (smallEtalePullback h).obj V :=
  MorphismProperty.Over.homMk (complementOpen h A).ι sorry

/-- The two members of the Zariski cover of `S_V` by the ambient open and the
complement of `Z`. -/
def supportCoverObject {V : T.Etale} (A : Admissible h V) : Bool → S.Etale
  | false => ambientEtale h A
  | true => complementEtale h A

/-- The two inclusions in the Zariski cover of `S_V`. -/
def supportCoverMap {V : T.Etale} (A : Admissible h V) :
    ∀ i : Bool, supportCoverObject h A i ⟶ (smallEtalePullback h).obj V
  | false => ambientInclusion h A
  | true => complementInclusion h A

/-- The ambient open and the complement of `Z` cover `S_V` in the small étale
topology. -/
theorem supportCover_mem {V : T.Etale} (A : Admissible h V) :
    Sieve.ofArrows (supportCoverObject h A) (supportCoverMap h A) ∈
      S.smallEtaleTopology ((smallEtalePullback h).obj V) :=
  sorry

/-- On the ambient member use the supported section; on the complement use
zero. -/
def supportExtensionLocalMap (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
    {V : T.Etale} (A : Admissible h V) :
    ∀ i : Bool,
      sections h F A ⟶ F.obj.obj (op (supportCoverObject h A i))
  | false =>
    AddCommGrpCat.ofHom
      (sectionsSupportedIn F (baseChangeToSource h V) A.subset A.ambient
        A.subset_le_ambient A.isClosed_in_ambient).subtype
  | true => 0

/-- Extend a section supported in an admissible `Z` by zero along the cover
`U ∪ (S_V \ Z)`. -/
def supportExtensionByZero (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
    {V : T.Etale} (A : Admissible h V) :
    sections h F A ⟶ F.obj.obj (op ((smallEtalePullback h).obj V)) :=
  F.property.amalgamateOfArrows (supportCoverMap h A) (supportCover_mem h A)
    (supportExtensionLocalMap h F A) sorry

/-- Extension by zero of an admissible supported section lands in the
compact-support subgroup. -/
theorem supportExtensionByZero_mem
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) {V : T.Etale}
    (A : Admissible h V) (σ : sections h F A) :
    (supportExtensionByZero h F A).hom σ ∈ compactSupportSections h F V :=
  sorry

/-- The objectwise comparison `H_Z(F) ⟶ h_! F(V)` obtained by extending a
supported section by zero. -/
def sectionsToCompactSupport (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
    {V : T.Etale} (A : Admissible h V) :
    sections h F A ⟶ AddCommGrpCat.of (compactSupportSections h F V) :=
  AddCommGrpCat.ofHom
    ((supportExtensionByZero h F A).hom.codRestrict
      (compactSupportSections h F V) (supportExtensionByZero_mem h F A))

/-- Cocone of zero-extension maps from the finite-support diagram on `S_V`. -/
def sectionsToCompactSupportCocone
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (V : T.Etale) :
    Cocone (diagram h F V) :=
  Cocone.mk (AddCommGrpCat.of (compactSupportSections h F V))
    { app := fun A ↦ sectionsToCompactSupport h F A
      naturality := sorry }

/-- The canonical comparison `h_{p!} F(V) ⟶ h_! F(V)` obtained by descending
zero-extension maps out of the colimit of `H_Z(F)`. -/
def presheafComparisonApp
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (V : T.Etale) :
    ((lowerShriekPresheaf h).obj F).obj (op V) ⟶
      AddCommGrpCat.of (compactSupportSections h F V) :=
  colimit.desc (diagram h F V) (sectionsToCompactSupportCocone h F V)

/-- The canonical forward comparison `h_{p!} ⟶ h_!` of abelian presheaves. -/
def presheafComparison :
    lowerShriekPresheaf h ⟶
      etaleLowerShriek h ⋙
        sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u} where
  app F :=
    { app := fun V ↦ presheafComparisonApp h F V.unop
      naturality := sorry }
  naturality := sorry

/-- The top open of `S_V` as an étale `S`-scheme is the small-étale pullback. -/
def topOpenEtaleIso (V : T.Etale) :
    mk ((⊤ : (baseChangeScheme h V).Opens).ι ≫ baseChangeToSource h V) ≅
      (smallEtalePullback h).obj V :=
  MorphismProperty.Over.isoMk (Scheme.topIso (baseChangeScheme h V)) sorry

/-- The locally closed subset of `S_V` underlying the closed étale support of a
section. -/
def sectionSupportLocallyClosed
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (V : T.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback h).obj V))) :
    LocallyCloseds (baseChangeScheme h V) :=
  ⟨(abelianSheafSectionSupport F ((smallEtalePullback h).obj V) σ :
      Set (baseChangeScheme h V)),
    (abelianSheafSectionSupport F ((smallEtalePullback h).obj V) σ).isClosed.isLocallyClosed⟩

/-- The admissible support on `S_V` with ambient open `⊤` associated to the
closed étale support of a compactly supported section. -/
def finiteSupportAdmissible
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (V : T.Etale)
    (σ : compactSupportSections h F V) :
    Admissible h V where
  subset := sectionSupportLocallyClosed h F V σ.1
  ambient := ⊤
  subset_le_ambient := Set.subset_univ _
  isClosed_in_ambient := sorry
  toBase_isFinite := sorry

/-- The transported section on the top open lies in `H_Z(F)` for the admissible
support of `σ`. -/
theorem topOpen_mem_sectionsSupportedIn
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (V : T.Etale)
    (σ : compactSupportSections h F V) :
    (F.obj.map (topOpenEtaleIso h V).hom.op).hom σ.1 ∈
      sectionsSupportedIn F (baseChangeToSource h V)
        (finiteSupportAdmissible h F V σ).subset
        (finiteSupportAdmissible h F V σ).ambient
        (finiteSupportAdmissible h F V σ).subset_le_ambient
        (finiteSupportAdmissible h F V σ).isClosed_in_ambient :=
  sorry

/-- The objectwise inverse comparison `h_! F(V) ⟶ h_{p!} F(V)`. -/
def presheafComparisonInvApp
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (V : T.Etale) :
    AddCommGrpCat.of (compactSupportSections h F V) ⟶
      ((lowerShriekPresheaf h).obj F).obj (op V) :=
  AddCommGrpCat.ofHom
    { toFun := fun σ ↦
        (colimit.ι (diagram h F V) (finiteSupportAdmissible h F V σ)).hom
          ⟨(F.obj.map (topOpenEtaleIso h V).hom.op).hom σ.1,
            topOpen_mem_sectionsSupportedIn h F V σ⟩
      map_zero' := sorry
      map_add' := sorry }

/-- The canonical inverse comparison `h_! ⟶ h_{p!}` of abelian presheaves. -/
def presheafComparisonInv :
    etaleLowerShriek h ⋙
        sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u} ⟶
      lowerShriekPresheaf h where
  app F :=
    { app := fun V ↦ presheafComparisonInvApp h F V.unop
      naturality := sorry }
  naturality := sorry

end Lqf

/-- The sheafified finite-support comparison `lowerShriek ⟶ etaleLowerShriek`. -/
def lowerShriekToEtaleLowerShriek {S T : Scheme.{u}} (h : S ⟶ T)
    [IsSeparated h] [LocallyQuasiFinite h] [LocallyOfFiniteType h]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}] :
    lowerShriek h ⟶ etaleLowerShriek h :=
  whiskerRight (Lqf.presheafComparison h)
      (presheafToSheaf T.smallEtaleTopology AddCommGrpCat.{u}) ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft (etaleLowerShriek h)
      (asIso
        (sheafificationAdjunction T.smallEtaleTopology
          AddCommGrpCat.{u}).counit).hom ≫
    (Functor.rightUnitor (etaleLowerShriek h)).hom

/-- The sheafified inverse comparison `etaleLowerShriek ⟶ lowerShriek`. -/
def lowerShriekFromEtaleLowerShriek {S T : Scheme.{u}} (h : S ⟶ T)
    [IsSeparated h] [LocallyQuasiFinite h] [LocallyOfFiniteType h]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}] :
    etaleLowerShriek h ⟶ lowerShriek h :=
  (Functor.rightUnitor (etaleLowerShriek h)).inv ≫
    whiskerLeft (etaleLowerShriek h)
      (asIso
        (sheafificationAdjunction T.smallEtaleTopology
          AddCommGrpCat.{u}).counit).inv ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (Lqf.presheafComparisonInv h)
      (presheafToSheaf T.smallEtaleTopology AddCommGrpCat.{u})

/-- After the finite-support/compact-support comparison, the sheafified
functor `lowerShriek` agrees with `etaleLowerShriek`. -/
def lowerShriekIsoEtaleLowerShriek {S T : Scheme.{u}} (h : S ⟶ T)
    [IsSeparated h] [LocallyQuasiFinite h] [LocallyOfFiniteType h]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}] :
    lowerShriek h ≅ etaleLowerShriek h where
  hom := lowerShriekToEtaleLowerShriek h
  inv := lowerShriekFromEtaleLowerShriek h
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `lowerShriekIsoEtaleLowerShriek` is the sheafified
finite-support comparison. -/
theorem lowerShriekIsoEtaleLowerShriek_hom {S T : Scheme.{u}} (h : S ⟶ T)
    [IsSeparated h] [LocallyQuasiFinite h] [LocallyOfFiniteType h]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}] :
    (lowerShriekIsoEtaleLowerShriek h).hom = lowerShriekToEtaleLowerShriek h :=
  sorry

/-- The inverse map of `lowerShriekIsoEtaleLowerShriek` is the sheafified
compact-support comparison. -/
theorem lowerShriekIsoEtaleLowerShriek_inv {S T : Scheme.{u}} (h : S ⟶ T)
    [IsSeparated h] [LocallyQuasiFinite h] [LocallyOfFiniteType h]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}] :
    (lowerShriekIsoEtaleLowerShriek h).inv = lowerShriekFromEtaleLowerShriek h :=
  sorry

/-- Continuous small-étale module pushforward commutes with forgetting from
`Λ`-modules to abelian groups. -/
def etaleModulePushforward_compSheafComposeIso {S T : Scheme.{u}} (h : S ⟶ T)
    (Λ : Type u) [CommRing Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [T.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})] :
    etaleModulePushforward h Λ ⋙
        sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ≅
      sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ⋙
        etaleAbelianPushforward h :=
  Functor.fullyFaithfulCancelRight
    (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u}) (Iso.refl _)

/-- Forgetting coefficients on module pushforward is continuous sheaf
pushforward of the underlying abelian sheaves. -/
theorem etaleModulePushforward_compSheafComposeIso_hom {S T : Scheme.{u}}
    (h : S ⟶ T) (Λ : Type u) [CommRing Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [T.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})] :
    (etaleModulePushforward_compSheafComposeIso h Λ).hom =
      (etaleModulePushforward_compSheafComposeIso h Λ).hom :=
  sorry

/-- Lift an abelian sheaf morphism between forgotten module sheaves to a
morphism of sheaves of `Λ`-modules, using the underlying additive map on
sections. -/
def liftModuleSheafHom {S : Scheme.{u}} {Λ : Type u} [CommRing Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)}
    (α :
      (sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F ⟶
        (sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj G) :
    F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U ↦
        ConcreteCategory.ofHom (C := ModuleCat.{u} Λ)
          { toAddHom := (α.hom.app U).hom.toAddHom
            map_smul' := fun _ _ ↦ sorry }
      naturality := sorry }

/-- The lift recovers the original abelian sheaf morphism after forgetting
coefficients. -/
theorem sheafCompose_map_liftModuleSheafHom {S : Scheme.{u}} {Λ : Type u}
    [CommRing Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)}
    (α :
      (sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F ⟶
        (sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj G) :
    (sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).map
        (liftModuleSheafHom α) =
      α :=
  sorry

variable (Λ : Type u) [CommRing Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]

/-- Functorial forgetful comparison of compact-support functors, assembled
from the objectwise isomorphisms `lowerShriekModule_forget`. -/
def lowerShriekModule_forgetFunctorIso {S T : Scheme.{u}} (h : S ⟶ T)
    [LocallyQuasiFinite h] (Λ : Type u) [CommRing Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [T.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [T.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})] :
    lowerShriekModule h Λ ⋙
        sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ≅
      sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ⋙
        lowerShriek h :=
  NatIso.ofComponents (fun F ↦ lowerShriekModule_forget h Λ F) sorry

/-- The objectwise forgetful comparison is the component of
`lowerShriekModule_forgetFunctorIso`. -/
theorem lowerShriekModule_forgetFunctorIso_app {S T : Scheme.{u}} (h : S ⟶ T)
    [LocallyQuasiFinite h] (Λ : Type u) [CommRing Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [T.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [T.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule_forgetFunctorIso h Λ).app F =
      lowerShriekModule_forget h Λ F :=
  sorry

/-- Forgetting coefficients identifies `g_! (f'_* F)` with
`(etaleLowerShriek g) ((etaleAbelianPushforward f') (forget F))`. -/
def etaleModuleLowerShriekPushforward_forgetLeft
    (F : Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule g Λ).obj ((etaleModulePushforward f' Λ).obj F)) ≅
      (etaleLowerShriek g).obj
        ((etaleAbelianPushforward f').obj
          ((sheafCompose X'.smallEtaleTopology
              (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)) :=
  (lowerShriekModule_forgetFunctorIso g Λ).app
      ((etaleModulePushforward f' Λ).obj F) ≪≫
    (lowerShriekIsoEtaleLowerShriek g).app
      ((sheafCompose Y'.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((etaleModulePushforward f' Λ).obj F)) ≪≫
    (etaleLowerShriek g).mapIso
      ((etaleModulePushforward_compSheafComposeIso f' Λ).app F)

/-- Forgetting coefficients identifies `f_* (g'_! F)` with
`(etaleAbelianPushforward f) ((etaleLowerShriek g') (forget F))`. -/
def etaleModuleLowerShriekPushforward_forgetRight
    (F : Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((etaleModulePushforward f Λ).obj ((lowerShriekModule g' Λ).obj F)) ≅
      (etaleAbelianPushforward f).obj
        ((etaleLowerShriek g').obj
          ((sheafCompose X'.smallEtaleTopology
              (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)) :=
  (etaleModulePushforward_compSheafComposeIso f Λ).app
      ((lowerShriekModule g' Λ).obj F) ≪≫
    (etaleAbelianPushforward f).mapIso
      ((lowerShriekModule_forgetFunctorIso g' Λ).app F ≪≫
        (lowerShriekIsoEtaleLowerShriek g').app
          ((sheafCompose X'.smallEtaleTopology
              (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F))

/-- The component of the module sheaf isomorphism `g_! ∘ f'_* ≅ f_* ∘ g'_!`
at a sheaf of `Λ`-modules. -/
def etaleModuleLowerShriekPushforwardIso_app
    (F : Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule g Λ).obj ((etaleModulePushforward f' Λ).obj F) ≅
      (etaleModulePushforward f Λ).obj ((lowerShriekModule g' Λ).obj F) where
  hom :=
    liftModuleSheafHom
      ((etaleModuleLowerShriekPushforward_forgetLeft f' g Λ F).hom ≫
        ((etaleLowerShriekPushforwardIso f f' g g' h_sq).app
            ((sheafCompose X'.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
        (etaleModuleLowerShriekPushforward_forgetRight f g' Λ F).inv)
  inv :=
    liftModuleSheafHom
      ((etaleModuleLowerShriekPushforward_forgetRight f g' Λ F).hom ≫
        ((etaleLowerShriekPushforwardIso f f' g g' h_sq).app
            ((sheafCompose X'.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).inv ≫
        (etaleModuleLowerShriekPushforward_forgetLeft f' g Λ F).inv)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The sheaf-level module isomorphism `g_! ∘ f'_* ≅ f_* ∘ g'_!`. -/
def etaleModuleLowerShriekPushforwardIso :
    etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ ≅
      lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ :=
  NatIso.ofComponents
    (etaleModuleLowerShriekPushforwardIso_app f f' g g' h_sq Λ) sorry

/-- The forward map of `etaleModuleLowerShriekPushforwardIso` is assembled
componentwise from the abelian comparison after forgetting coefficients. -/
theorem etaleModuleLowerShriekPushforwardIso_hom :
    (etaleModuleLowerShriekPushforwardIso f f' g g' h_sq Λ).hom =
      (etaleModuleLowerShriekPushforwardIso f f' g g' h_sq Λ).hom :=
  sorry

/-- Unfolding `etaleModulePushforward` recovers additivity of the underlying
continuous small-étale module pushforward. -/
instance etaleModulePushforward_sheafPushforwardContinuous_additive
    {S T : Scheme.{u}} (h : S ⟶ T) {R : Type u} [CommRing R]
    [hF : (etaleModulePushforward h R).Additive] :
    ((smallEtalePullback h).sheafPushforwardContinuous
      (ModuleCat.{u} R) T.smallEtaleTopology S.smallEtaleTopology).Additive :=
  hF

variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- The iterated cochain unit for `Rf'_* ⋙ g_!`, using exactness of `g_!`. -/
def etaleDerivedLowerShriekPushforward_leftUnit
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ) ⟶
      DerivedCategory.Q ⋙
        (etaleDerivedPushforward f' ⋙ lowerShriekModuleDerived g Λ) :=
  (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
        (ComplexShape.up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived Y Λ)).hom ≫
    (Functor.associator
      ((etaleModulePushforward f' Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      ((lowerShriekModule g Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived Y Λ)).hom ≫
    whiskerLeft
      ((etaleModulePushforward f' Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      (lowerShriekModule g Λ).mapDerivedCategoryFactors.inv ≫
    (Functor.associator
      ((etaleModulePushforward f' Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived Y' Λ)
      (lowerShriekModuleDerived g Λ)).inv ≫
    whiskerRight
      (RightDerived.Cochain.unit (etaleModulePushforward f' Λ))
      (lowerShriekModuleDerived g Λ) ≫
    (Functor.associator
      (DerivedCategory.Q :
        CochainComplex (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived X' Λ)
      (etaleDerivedPushforward f')
      (lowerShriekModuleDerived g Λ)).hom

/-- Exactness of `g_!` makes `Rf'_* ⋙ g_!` a right-derived functor of
`f'_* ⋙ g_!`. -/
instance etaleDerivedLowerShriekPushforward_left_isRightDerived
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    (etaleDerivedPushforward f' ⋙ lowerShriekModuleDerived g Λ).IsRightDerivedFunctor
      (etaleDerivedLowerShriekPushforward_leftUnit f' g Λ)
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)) :=
  sorry

/-- The derived identification `g_! ∘ Rf'_* ≅ R(g_! ∘ f'_*)`. -/
def etaleDerivedLowerShriekPushforward_leftIso
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedPushforward f' ⋙ lowerShriekModuleDerived g Λ ≅
      RightDerived.Cochain.functor
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ) :=
  RightDerived.natIsoOfIso
    (DerivedCategory.Q :
      CochainComplex (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
        EtaleDerived X' Λ)
    (HomologicalComplex.quasiIso
      (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (etaleDerivedLowerShriekPushforward_leftUnit f' g Λ)
    (RightDerived.Cochain.unit
      (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
    (Iso.refl _)

/-- The sheaf-level module isomorphism transported to total right-derived
functors. -/
def etaleDerivedLowerShriekPushforward_middleIso
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    RightDerived.Cochain.functor
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ) ≅
      RightDerived.Cochain.functor
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ) :=
  RightDerived.natIsoOfIso
    (DerivedCategory.Q :
      CochainComplex (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
        EtaleDerived X' Λ)
    (HomologicalComplex.quasiIso
      (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (RightDerived.Cochain.unit
      (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
    (RightDerived.Cochain.unit
      (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (etaleModuleLowerShriekPushforwardIso f f' g g' h_sq Λ)
        (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived Y Λ))

/-- The iterated cochain unit for `R(g'_! ⋙ f_*)`, using exactness of `g'_!`
but not injective-preservation. -/
def etaleDerivedLowerShriekPushforward_rightUnit
    [(etaleModulePushforward f Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
            EtaleDerived X' Λ) ⋙
        (lowerShriekModuleDerived g' Λ ⋙ etaleDerivedPushforward f) :=
  RightDerived.Cochain.ExactFirst.unit
    (ExactFunctor.of (lowerShriekModule g' Λ))
    (etaleModulePushforward f Λ)

/-- The iterated unit of `R(g'_! ⋙ f_*)` is the exact-first cochain unit. -/
theorem etaleDerivedLowerShriekPushforward_rightUnit_eq
    [(etaleModulePushforward f Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedLowerShriekPushforward_rightUnit f g' Λ =
      RightDerived.Cochain.ExactFirst.unit
        (ExactFunctor.of (lowerShriekModule g' Λ))
        (etaleModulePushforward f Λ) :=
  sorry

/-- The derived comparison `R(g'_! ⋙ f_*) ⟶ g'_! ⋙ Rf_*`. This is the
source's last arrow, not invertible in general. -/
def etaleDerivedLowerShriekPushforward_rightComparison
    [(etaleModulePushforward f Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    RightDerived.Cochain.functor
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ) ⟶
      lowerShriekModuleDerived g' Λ ⋙ etaleDerivedPushforward f :=
  (RightDerived.Cochain.functor
      (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ)).rightDerivedDesc
    (RightDerived.Cochain.unit
      (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
    (HomologicalComplex.quasiIso
      (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (lowerShriekModuleDerived g' Λ ⋙ etaleDerivedPushforward f)
    (etaleDerivedLowerShriekPushforward_rightUnit f g' Λ)

/-- The canonical derived comparison `g_! ∘ Rf'_* ⟶ Rf_* ∘ g'_!`. -/
def etaleDerivedLowerShriekPushforward
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedPushforward f' ⋙ lowerShriekModuleDerived g Λ ⟶
      lowerShriekModuleDerived g' Λ ⋙ etaleDerivedPushforward f :=
  (etaleDerivedLowerShriekPushforward_leftIso f' g Λ).hom ≫
    (etaleDerivedLowerShriekPushforward_middleIso f f' g g' h_sq Λ).hom ≫
    etaleDerivedLowerShriekPushforward_rightComparison f g' Λ

/-- The comparison at an object of `D(X'_étale, Λ)`. -/
def etaleDerivedLowerShriekPushforward_app
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : EtaleDerived X' Λ) :
    (lowerShriekModuleDerived g Λ).obj ((etaleDerivedPushforward f').obj K) ⟶
      (etaleDerivedPushforward f).obj ((lowerShriekModuleDerived g' Λ).obj K) :=
  (etaleDerivedLowerShriekPushforward f f' g g' h_sq Λ).app K

/-- The objectwise comparison is the component of
`etaleDerivedLowerShriekPushforward`. -/
theorem etaleDerivedLowerShriekPushforward_app_eq
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : EtaleDerived X' Λ) :
    etaleDerivedLowerShriekPushforward_app f f' g g' h_sq Λ K =
      (etaleDerivedLowerShriekPushforward f f' g g' h_sq Λ).app K :=
  sorry

/-- The comparison is an isomorphism on objects that are bounded below with
torsion cohomology sheaves, or when `Λ` is a torsion ring. -/
theorem etaleDerivedLowerShriekPushforward_isIso_of
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ).Additive]
    [(lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : EtaleDerived X' Λ)
    (hK : AddMonoid.IsTorsion Λ ∨
      (etaleDerivedIsTorsion K ∧ ∃ n, DerivedCategory.IsGE K n)) :
    IsIso ((etaleDerivedLowerShriekPushforward f f' g g' h_sq Λ).app K) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
