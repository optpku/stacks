module

public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Presheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek

/-!
# Finite-support and compact-support lower shriek

For a separated locally quasi-finite morphism, zero extension identifies the
finite-support colimit presheaf with the underlying compact-support sheaf.
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
theorem FiniteSupport.Admissible.isClosed {V : Y.Etale} (A : Admissible f V) :
    IsClosed (A.subset : Set (baseChangeScheme f V)) :=
  sorry

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private implementation to the public comparison definitions.
set_option backward.privateInPublic true in
/-- The étale `X`-scheme cut out by the ambient open of an admissible
support. -/
private def ambientEtale {V : Y.Etale} (A : Admissible f V) : X.Etale :=
  mk (A.ambient.ι ≫ baseChangeToSource f V)

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private implementation to the public comparison definitions.
set_option backward.privateInPublic true in
/-- The open complement of an admissible support in `X_V`. -/
private def complementOpen {V : Y.Etale} (A : Admissible f V) :
    (baseChangeScheme f V).Opens :=
  ⟨(A.subset : Set (baseChangeScheme f V))ᶜ,
    (FiniteSupport.Admissible.isClosed f A).isOpen_compl⟩

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private implementation to the public comparison definitions.
set_option backward.privateInPublic true in
/-- The étale `X`-scheme cut out by the complement of an admissible support. -/
private def complementEtale {V : Y.Etale} (A : Admissible f V) : X.Etale :=
  mk ((complementOpen f A).ι ≫ baseChangeToSource f V)

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private implementation to the public comparison definitions.
set_option backward.privateInPublic true in
/-- The inclusion of the ambient étale object into the base change `X_V`. -/
private def ambientInclusion {V : Y.Etale} (A : Admissible f V) :
    ambientEtale f A ⟶ (smallEtalePullback f).obj V :=
  MorphismProperty.Over.homMk A.ambient.ι rfl

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private implementation to the public comparison definitions.
set_option backward.privateInPublic true in
/-- The inclusion of the complementary étale object into the base change
`X_V`. -/
private def complementInclusion {V : Y.Etale} (A : Admissible f V) :
    complementEtale f A ⟶ (smallEtalePullback f).obj V :=
  MorphismProperty.Over.homMk (complementOpen f A).ι rfl

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private implementation to the public comparison definitions.
set_option backward.privateInPublic true in
/-- The two members of the Zariski cover of `X_V` by the ambient open and the
complement of `Z`. -/
private def supportCoverObject {V : Y.Etale} (A : Admissible f V) : Bool → X.Etale
  | false => ambientEtale f A
  | true => complementEtale f A

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private implementation to the public comparison definitions.
set_option backward.privateInPublic true in
/-- The two inclusions in the Zariski cover of `X_V` by the ambient open and the
complement of `Z`. -/
private def supportCoverMap {V : Y.Etale} (A : Admissible f V) :
    ∀ i : Bool, supportCoverObject f A i ⟶ (smallEtalePullback f).obj V
  | false => ambientInclusion f A
  | true => complementInclusion f A

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private implementation to the public comparison definitions.
set_option backward.privateInPublic true in
/-- The ambient open and the complement of `Z` cover `X_V` in the small étale
topology. -/
private theorem supportCover_mem {V : Y.Etale} (A : Admissible f V) :
    Sieve.ofArrows (supportCoverObject f A) (supportCoverMap f A) ∈
      X.smallEtaleTopology ((smallEtalePullback f).obj V) :=
  sorry

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private implementation to the public comparison definitions.
set_option backward.privateInPublic true in
/-- On the ambient member use the supported section; on the complement use
zero. -/
private def supportExtensionLocalMap (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V : Y.Etale} (A : Admissible f V) :
    ∀ i : Bool,
      sections f F A ⟶ F.obj.obj (op (supportCoverObject f A i))
  | false =>
    AddCommGrpCat.ofHom
      (sectionsSupportedIn F (baseChangeToSource f V) A.subset A.ambient
        A.subset_le_ambient A.isClosed_in_ambient).subtype
  | true => 0

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private implementation to the public comparison definitions.
set_option backward.privateInPublic true in
/-- The supported section on the ambient open and zero on the complement agree
on every overlap. -/
private theorem supportExtensionLocalMap_compatible
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V : Y.Etale}
    (A : Admissible f V) :
    ∀ (W : X.Etale) (i k : Bool) (a : W ⟶ supportCoverObject f A i)
      (b : W ⟶ supportCoverObject f A k),
      a ≫ supportCoverMap f A i = b ≫ supportCoverMap f A k →
        supportExtensionLocalMap f F A i ≫ F.obj.map a.op =
          supportExtensionLocalMap f F A k ≫ F.obj.map b.op :=
  sorry

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator requires access to the private cover and gluing maps.
set_option backward.privateInPublic true in
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
  rfl

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private implementation to the public comparison definitions.
set_option backward.privateInPublic true in
/-- Cocone of zero-extension maps from the finite-support diagram on `X_V`. -/
private def sectionsToCompactSupportCocone
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    Cocone (diagram f F V) :=
  Cocone.mk (AddCommGrpCat.of (compactSupportSections f F V))
    { app := fun A ↦ sectionsToCompactSupport f F A
      naturality := sorry }

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator requires access to the private zero-extension cocone.
set_option backward.privateInPublic true in
/-- The canonical comparison `f_{p!} F(V) ⟶ f_! F(V)` obtained by descending
zero-extension maps out of the colimit of `H_Z(F)`. -/
def lowerShriekPresheafComparisonApp
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    ((lowerShriekPresheaf f).obj F).obj (op V) ⟶
      AddCommGrpCat.of (compactSupportSections f F V) :=
  colimit.desc (diagram f F V) (sectionsToCompactSupportCocone f F V)

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
  rfl

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private implementation to the public comparison definitions.
set_option backward.privateInPublic true in
/-- The top open of `X_V` as an étale `X`-scheme is canonically the small-étale
pullback object `(smallEtalePullback f).obj V`. -/
private def topOpenEtaleIso (V : Y.Etale) :
    mk ((⊤ : (baseChangeScheme f V).Opens).ι ≫ baseChangeToSource f V) ≅
      (smallEtalePullback f).obj V :=
  MorphismProperty.Over.isoMk (Scheme.topIso (baseChangeScheme f V)) sorry

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private implementation to the public comparison definitions.
set_option backward.privateInPublic true in
/-- The locally closed subset of `X_V` underlying the closed étale support of a
section. -/
private def sectionSupportLocallyClosed
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) :
    LocallyCloseds (baseChangeScheme f V) :=
  ⟨(abelianSheafSectionSupport F ((smallEtalePullback f).obj V) σ :
      Set (baseChangeScheme f V)),
    (abelianSheafSectionSupport F ((smallEtalePullback f).obj V) σ).isClosed.isLocallyClosed⟩

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator requires access to the private locally closed support view.
set_option backward.privateInPublic true in
/-- The admissible support on `X_V` with ambient open `⊤` associated to the
closed étale support of a compactly supported section. -/
def FiniteSupport.Admissible.ofCompactSupport (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) (σ : compactSupportSections f F V) :
    Admissible f V where
  subset := sectionSupportLocallyClosed f F V σ.1
  ambient := ⊤
  subset_le_ambient := Set.subset_univ _
  isClosed_in_ambient := sorry
  toBase_isFinite := sorry

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator requires access to the private locally closed support view in its statement.
set_option backward.privateInPublic true in
/-- The admissible support of a compactly supported section records its étale
section support with ambient open `⊤`. -/
theorem FiniteSupport.Admissible.ofCompactSupport_spec
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections f F V) :
    (FiniteSupport.Admissible.ofCompactSupport f F V σ).subset =
      sectionSupportLocallyClosed f F V σ.1 ∧
      (FiniteSupport.Admissible.ofCompactSupport f F V σ).ambient = ⊤ :=
  ⟨rfl, rfl⟩

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private implementation to the public comparison definitions.
set_option backward.privateInPublic true in
/-- The transported section on the top open lies in `H_Z(F)` for the admissible
support of `σ`. -/
private theorem topOpen_mem_sectionsSupportedIn
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections f F V) :
    (F.obj.map (topOpenEtaleIso f V).hom.op).hom σ.1 ∈
      sectionsSupportedIn F (baseChangeToSource f V)
        (FiniteSupport.Admissible.ofCompactSupport f F V σ).subset
        (FiniteSupport.Admissible.ofCompactSupport f F V σ).ambient
        (FiniteSupport.Admissible.ofCompactSupport f F V σ).subset_le_ambient
        (FiniteSupport.Admissible.ofCompactSupport f F V σ).isClosed_in_ambient :=
  sorry

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator requires access to the private top-open transport and its support proof.
set_option backward.privateInPublic true in
/-- The objectwise inverse comparison `f_! F(V) ⟶ f_{p!} F(V)` sending a
compactly supported section to its class in the colimit of `H_Z(F)`. -/
def lowerShriekPresheafComparisonInvApp
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    AddCommGrpCat.of (compactSupportSections f F V) ⟶
      ((lowerShriekPresheaf f).obj F).obj (op V) :=
  AddCommGrpCat.ofHom
    { toFun := fun σ ↦
        (colimit.ι (diagram f F V) (FiniteSupport.Admissible.ofCompactSupport f F V σ)).hom
          ⟨(F.obj.map (topOpenEtaleIso f V).hom.op).hom σ.1,
            topOpen_mem_sectionsSupportedIn f F V σ⟩
      map_zero' := sorry
      map_add' := sorry }

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator requires access to the private top-open transport and its support proof in its statement.
set_option backward.privateInPublic true in
/-- The objectwise inverse comparison is the indicated colimit coprojection. -/
theorem lowerShriekPresheafComparisonInvApp_apply
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections f F V) :
    (lowerShriekPresheafComparisonInvApp f F V).hom σ =
      (colimit.ι (diagram f F V) (FiniteSupport.Admissible.ofCompactSupport f F V σ)).hom
        ⟨(F.obj.map (topOpenEtaleIso f V).hom.op).hom σ.1,
          topOpen_mem_sectionsSupportedIn f F V σ⟩ :=
  rfl

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
  rfl

/-- For a separated locally quasi-finite morphism, the finite-support presheaf
is canonically naturally isomorphic to the underlying compact-support sheaf. -/
@[stacks 0F6N]
def lowerShriekPresheafIso :
    lowerShriekPresheaf f ≅
      etaleLowerShriek f ⋙
        sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u} where
  hom := lowerShriekPresheafComparison f
  inv := lowerShriekPresheafComparisonInv f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The canonical finite-support identification at an abelian étale sheaf. -/
def lowerShriekPresheafIso_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriekPresheaf f).obj F ≅
      (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
        ((etaleLowerShriek f).obj F) :=
  (lowerShriekPresheafIso f).app F

/-- The objectwise identification is the component of `lowerShriekPresheafIso`. -/
theorem lowerShriekPresheafIso_app_eq
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    lowerShriekPresheafIso_app f F = (lowerShriekPresheafIso f).app F :=
  rfl

/-- The forward map of `lowerShriekPresheafIso` is the zero-extension
comparison. -/
theorem lowerShriekPresheafIso_hom :
    (lowerShriekPresheafIso f).hom = lowerShriekPresheafComparison f :=
  rfl

/-- The inverse map of `lowerShriekPresheafIso` is the colimit-coprojection
comparison. -/
theorem lowerShriekPresheafIso_inv :
    (lowerShriekPresheafIso f).inv = lowerShriekPresheafComparisonInv f :=
  rfl

/-- The finite-support presheaf of an abelian étale sheaf is a sheaf. -/
theorem lowerShriekPresheaf_isSheaf
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Presheaf.IsSheaf Y.smallEtaleTopology ((lowerShriekPresheaf f).obj F) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
