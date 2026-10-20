module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.«96_10_3_3_Comparison»
public import stacks_project.Chap103.Lemma_103_5_1_SmallSections
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap103.«103_15_1_1_Smooth»

/-!
# Étale-module rules on algebraic stacks

A rule `M` assigns to each algebraic stack a weak Serre subcategory of étale
`𝒪`-modules, stable under smooth inverse image, detected on jointly
point-covering smooth families, and stable under étale `R^i f_*` for morphisms
between stacks representable by affine schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- The category of étale `𝒪_X`-modules on the associated étale ringed site. -/
abbrev etaleModules (X : GroupoidsOver S) :=
  SheafOfModules.{u} (etaleRingedSite X).structureSheaf

/-- `etaleModules X` is the category of sheaves of modules on `etaleRingedSite X`. -/
theorem etaleModules_eq (X : GroupoidsOver S) :
    etaleModules X = SheafOfModules.{u} (etaleRingedSite X).structureSheaf :=
  sorry

/-- The category of étale `𝒪_X`-modules is abelian. -/
instance etaleModules_abelian (X : GroupoidsOver S) : Abelian (etaleModules X) :=
  GroupoidsOver.etaleModulesAbelian X

/-- The underived étale module pushforward `f_*`, as the concrete module
direct image along `etaleRingedToposHom f`. -/
def etaleModulePushforward {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [HasSmallCFGTypeSections f] :
    etaleModules X ⥤ etaleModules Y :=
  etaleModuleDirectImage f

/-- `etaleModulePushforward f` is `etaleModuleDirectImage f`. -/
theorem etaleModulePushforward_eq {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [HasSmallCFGTypeSections f] :
    etaleModulePushforward f = etaleModuleDirectImage f :=
  sorry

/-- Étale module direct image is additive. -/
instance etaleModulePushforward_additive {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [HasSmallCFGTypeSections f] :
    (etaleModulePushforward f).Additive :=
  RingedSite.ToposHom.modulePushforward_additive (etaleRingedToposHom f)

/-- Étale modules on a category fibred in groupoids admit injective
resolutions. -/
instance instHasInjectiveResolutions_etaleModules (X : GroupoidsOver S) :
    HasInjectiveResolutions (etaleModules X) :=
  sorry

/-- The degree-`i` étale higher direct image functor `R^i f_*` on étale
modules. -/
abbrev higherDirectImageFunctor {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [HasSmallCFGTypeSections f] (i : ℕ) :
    etaleModules X ⥤ etaleModules Y :=
  (etaleModulePushforward f).rightDerived i

/-- `higherDirectImageFunctor f i` is the degree-`i` right derived functor of
étale module direct image. -/
theorem higherDirectImageFunctor_eq {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [HasSmallCFGTypeSections f] (i : ℕ) :
    higherDirectImageFunctor f i = (etaleModulePushforward f).rightDerived i :=
  sorry

/-- The degree-`i` étale higher direct image `R^i f_* F`. -/
abbrev higherDirectImage {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [HasSmallCFGTypeSections f]
    (F : etaleModules X) (i : ℕ) : etaleModules Y :=
  (higherDirectImageFunctor f i).obj F

/-- `higherDirectImage f F i` is the object map of `higherDirectImageFunctor`. -/
theorem higherDirectImage_eq {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [HasSmallCFGTypeSections f]
    (F : etaleModules X) (i : ℕ) :
    higherDirectImage f F i = (higherDirectImageFunctor f i).obj F :=
  sorry

/-- An algebraic stack (or category fibred in groupoids) is representable by an
affine scheme if it is equivalent to the slice fibration of an affine scheme
over `S`. -/
def IsRepresentableByAffine (X : GroupoidsOver S) : Prop :=
  ∃ U : Over S, IsAffine U.left ∧ Nonempty (X ≌ GroupoidsOver.slice U)

/-- Representability by an affine scheme means equivalence with the slice of an
affine scheme over `S`. -/
theorem isRepresentableByAffine_iff (X : GroupoidsOver S) :
    IsRepresentableByAffine X ↔
      ∃ U : Over S, IsAffine U.left ∧ Nonempty (X ≌ GroupoidsOver.slice U) :=
  sorry

/-- The slice fibration of an affine scheme over `S` is representable by an
affine scheme. -/
theorem isRepresentableByAffine_slice (U : Over S) [IsAffine U.left] :
    IsRepresentableByAffine (GroupoidsOver.slice U) :=
  sorry

/-- A rule associating to every algebraic stack a subcategory of étale
`𝒪`-modules, subject to weak Serre, smooth inverse-image, covering-detection,
and affine higher-direct-image axioms. -/
structure EtaleModuleRule (S : Scheme.{u}) where
  /-- The subcategory of étale `𝒪_X`-modules attached to each algebraic stack. -/
  predicate (X : GroupoidsOver S) [AlgebraicStack X] :
    ObjectProperty (etaleModules X)
  /-- Each assigned subcategory is a weak Serre class. -/
  isWeakSerre (X : GroupoidsOver S) [AlgebraicStack X] :
    (predicate X).IsWeakSerreClass
  /-- Inverse image along a smooth morphism of algebraic stacks preserves the
  rule. -/
  mapsInverseImage_of_smooth {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f] :
    predicate Y ≤ (predicate X).inverseImage (etaleModuleInverseImage f)
  /-- Membership in the rule is detected on a jointly point-covering family of
  smooth morphisms of algebraic stacks. -/
  mem_iff_of_smoothCovering {X : GroupoidsOver S} [AlgebraicStack X]
      {ι : Type v} {Xi : ι → GroupoidsOver S} [∀ i, AlgebraicStack (Xi i)]
      (f : ∀ i, Xi i ⟶ X) [∀ i, Smooth (f i)]
      (h_cover : ∀ x : Points X, ∃ i, x ∈ Set.range (Points.map (f i)))
      (F : etaleModules X) :
    predicate X F ↔ ∀ i, predicate (Xi i) ((etaleModuleInverseImage (f i)).obj F)
  /-- Higher direct images in the étale topology preserve the rule when source
  and target are representable by affine schemes. -/
  mapsHigherDirectImage_of_affine {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      (hX : IsRepresentableByAffine X) (hY : IsRepresentableByAffine Y)
      (i : ℕ) {F : etaleModules X} (hF : predicate X F) :
    predicate Y ((higherDirectImageFunctor f i).obj F)

namespace EtaleModuleRule

/-- The maximal étale-module rule, sending every algebraic stack to the full
category of étale modules. -/
def max (S : Scheme.{u}) : EtaleModuleRule S where
  predicate _ := ⊤
  isWeakSerre := sorry
  mapsInverseImage_of_smooth := sorry
  mem_iff_of_smoothCovering := sorry
  mapsHigherDirectImage_of_affine := sorry

variable {S : Scheme.{u}} (M : EtaleModuleRule S)

/-- Inverse image along a smooth morphism sends objects of the rule on the
target into the rule on the source. -/
theorem mapsInverseImage_obj {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f]
    {F : etaleModules Y} (hF : M.predicate Y F) :
    M.predicate X ((etaleModuleInverseImage f).obj F) :=
  sorry

/-- Higher direct images in the étale topology send objects of the rule into
the rule, when source and target are representable by affine schemes. -/
theorem mapsHigherDirectImage_of_affine_obj {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (hX : IsRepresentableByAffine X) (hY : IsRepresentableByAffine Y)
    (i : ℕ) {F : etaleModules X} (hF : M.predicate X F) :
    M.predicate Y ((higherDirectImageFunctor f i).obj F) :=
  sorry

end EtaleModuleRule

end AlgebraicGeometry.AlgebraicStack

