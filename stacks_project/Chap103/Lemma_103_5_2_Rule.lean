module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import stacks_project.Chap96.Lemma_96_6_2_RingedTopos
public import stacks_project.Chap103.Lemma_103_5_1_Rule

/-!
# Fppf-module rules on algebraic stacks

A rule `M` assigns to each algebraic stack a weak Serre subcategory of fppf
`𝒪`-modules, stable under smooth inverse image, detected on jointly
point-covering smooth families, and stable under fppf `R^i f_*` for morphisms
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

/-- The category of fppf `𝒪_X`-modules on the associated fppf ringed site. -/
abbrev fppfModules (X : GroupoidsOver S) :=
  SheafOfModules.{u} (associatedRingedSite X StandardTopology.fppf).structureSheaf

/-- `fppfModules X` is the category of sheaves of modules on
`associatedRingedSite X StandardTopology.fppf`. -/
theorem fppfModules_eq (X : GroupoidsOver S) :
    fppfModules X =
      SheafOfModules.{u} (associatedRingedSite X StandardTopology.fppf).structureSheaf :=
  sorry

/-- The category of fppf `𝒪_X`-modules is abelian. -/
instance fppfModules_abelian (X : GroupoidsOver S) : Abelian (fppfModules X) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

/-- Inverse image `f^*` of fppf `𝒪`-modules along a 1-morphism, as module
pushforward along `toFunctorSiteHom f StandardTopology.fppf`. -/
def fppfModuleInverseImage {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    fppfModules Y ⥤ fppfModules X :=
  (toFunctorSiteHom f StandardTopology.fppf).modulePushforward.{u}

/-- `fppfModuleInverseImage f` is module pushforward along the associated fppf
ringed-site morphism. -/
theorem fppfModuleInverseImage_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    fppfModuleInverseImage f =
      (toFunctorSiteHom f StandardTopology.fppf).modulePushforward.{u} :=
  sorry

/-- The underived fppf module pushforward `f_*`, as the concrete module
direct image along `associatedRingedToposHom f StandardTopology.fppf`. -/
def fppfModulePushforward {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    fppfModules X ⥤ fppfModules Y :=
  (associatedRingedToposHom f StandardTopology.fppf).modulePushforward

/-- `fppfModulePushforward f` is the module direct image of the associated fppf
ringed-topos morphism. -/
theorem fppfModulePushforward_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    fppfModulePushforward f =
      (associatedRingedToposHom f StandardTopology.fppf).modulePushforward :=
  sorry

/-- Fppf module direct image is additive. -/
instance fppfModulePushforward_additive {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (fppfModulePushforward f).Additive :=
  RingedSite.ToposHom.modulePushforward_additive
    (associatedRingedToposHom f StandardTopology.fppf)

/-- Fppf modules on a category fibred in groupoids admit injective resolutions. -/
instance instHasInjectiveResolutions_fppfModules (X : GroupoidsOver S) :
    HasInjectiveResolutions (fppfModules X) :=
  sorry

/-- The degree-`i` fppf higher direct image functor `R^i f_*` on fppf modules. -/
abbrev fppfHigherDirectImageFunctor {X Y : GroupoidsOver S} (f : X ⟶ Y) (i : ℕ) :
    fppfModules X ⥤ fppfModules Y :=
  (fppfModulePushforward f).rightDerived i

/-- `fppfHigherDirectImageFunctor f i` is the degree-`i` right derived functor of
fppf module direct image. -/
theorem fppfHigherDirectImageFunctor_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) (i : ℕ) :
    fppfHigherDirectImageFunctor f i = (fppfModulePushforward f).rightDerived i :=
  sorry

/-- The degree-`i` fppf higher direct image `R^i f_* F`. -/
abbrev fppfHigherDirectImage {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (F : fppfModules X) (i : ℕ) : fppfModules Y :=
  (fppfHigherDirectImageFunctor f i).obj F

/-- `fppfHigherDirectImage f F i` is the object map of `fppfHigherDirectImageFunctor`. -/
theorem fppfHigherDirectImage_eq {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (F : fppfModules X) (i : ℕ) :
    fppfHigherDirectImage f F i = (fppfHigherDirectImageFunctor f i).obj F :=
  sorry

/-- A rule associating to every algebraic stack a subcategory of fppf
`𝒪`-modules, subject to weak Serre, smooth inverse-image, covering-detection,
and affine higher-direct-image axioms. -/
structure FppfModuleRule (S : Scheme.{u}) where
  /-- The subcategory of fppf `𝒪_X`-modules attached to each algebraic stack. -/
  predicate (X : GroupoidsOver S) [AlgebraicStack X] :
    ObjectProperty (fppfModules X)
  /-- Each assigned subcategory is a weak Serre class. -/
  isWeakSerre (X : GroupoidsOver S) [AlgebraicStack X] :
    (predicate X).IsWeakSerreClass
  /-- Inverse image along a smooth morphism of algebraic stacks preserves the
  rule. -/
  mapsInverseImage_of_smooth {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f] :
    predicate Y ≤ (predicate X).inverseImage (fppfModuleInverseImage f)
  /-- Membership in the rule is detected on a jointly point-covering family of
  smooth morphisms of algebraic stacks. -/
  mem_iff_of_smoothCovering {X : GroupoidsOver S} [AlgebraicStack X]
      {ι : Type v} {Xi : ι → GroupoidsOver S} [∀ i, AlgebraicStack (Xi i)]
      (f : ∀ i, Xi i ⟶ X) [∀ i, Smooth (f i)]
      (h_cover : ∀ x : Points X, ∃ i, x ∈ Set.range (Points.map (f i)))
      (F : fppfModules X) :
    predicate X F ↔ ∀ i, predicate (Xi i) ((fppfModuleInverseImage (f i)).obj F)
  /-- Higher direct images in the fppf topology preserve the rule when source
  and target are representable by affine schemes. -/
  mapsHigherDirectImage_of_affine {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      (hX : IsRepresentableByAffine X) (hY : IsRepresentableByAffine Y)
      (i : ℕ) {F : fppfModules X} (hF : predicate X F) :
    predicate Y ((fppfHigherDirectImageFunctor f i).obj F)

namespace FppfModuleRule

/-- The maximal fppf-module rule, sending every algebraic stack to the full
category of fppf modules. -/
def max (S : Scheme.{u}) : FppfModuleRule S where
  predicate _ := ⊤
  isWeakSerre := sorry
  mapsInverseImage_of_smooth := sorry
  mem_iff_of_smoothCovering := sorry
  mapsHigherDirectImage_of_affine := sorry

variable {S : Scheme.{u}} (M : FppfModuleRule S)

/-- Inverse image along a smooth morphism sends objects of the rule on the
target into the rule on the source. -/
theorem mapsInverseImage_obj {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f]
    {F : fppfModules Y} (hF : M.predicate Y F) :
    M.predicate X ((fppfModuleInverseImage f).obj F) :=
  sorry

/-- Higher direct images in the fppf topology send objects of the rule into
the rule, when source and target are representable by affine schemes. -/
theorem mapsHigherDirectImage_of_affine_obj {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (hX : IsRepresentableByAffine X) (hY : IsRepresentableByAffine Y)
    (i : ℕ) {F : fppfModules X} (hF : M.predicate X F) :
    M.predicate Y ((fppfHigherDirectImageFunctor f i).obj F) :=
  sorry

end FppfModuleRule

end AlgebraicGeometry.AlgebraicStack
