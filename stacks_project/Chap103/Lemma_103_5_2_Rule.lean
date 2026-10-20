module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Modules
public import stacks_project.Chap96.Lemma_96_6_2_RingedTopos
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import stacks_project.Chap103.Lemma_103_5_1_SmallSections
public import stacks_project.Chap103.«103_15_1_1_Smooth»

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

section ModuleAPI

variable (X : GroupoidsOver S) {Y : GroupoidsOver S} (f : X ⟶ Y)

#check (AlgebraicGeometry.AlgebraicStack.fppfModules X : Type (u + 1))
#check (AlgebraicGeometry.AlgebraicStack.fppfModules_eq X :
  fppfModules X =
    SheafOfModules.{u} (associatedRingedSite X StandardTopology.fppf).structureSheaf)
#check (AlgebraicGeometry.AlgebraicStack.fppfModules_abelian X : Abelian (fppfModules X))
#check (AlgebraicGeometry.AlgebraicStack.fppfModuleInverseImage f :
  fppfModules Y ⥤ fppfModules X)
#check (AlgebraicGeometry.AlgebraicStack.fppfModuleInverseImage_eq f :
  fppfModuleInverseImage f = @SheafOfModules.pushforward.{u, u, u, u + 1, u + 1, u}
    _ _ _ _ _ _ _ _ _ (toFunctor_isContinuous f StandardTopology.fppf)
    (associatedStructureSheafInverseImageIso f StandardTopology.fppf).inv)
#check (AlgebraicGeometry.AlgebraicStack.instHasInjectiveResolutions_fppfModules X :
  HasInjectiveResolutions (fppfModules X))

variable [HasSmallAssociatedTypeSections f StandardTopology.fppf]

#check (AlgebraicGeometry.AlgebraicStack.fppfModulePushforward f :
  fppfModules X ⥤ fppfModules Y)
#check (AlgebraicGeometry.AlgebraicStack.fppfModulePushforward_eq f :
  fppfModulePushforward f =
    @RingedSite.ToposHom.modulePushforward.{u + 1, u, u + 1, u, u}
      (associatedRingedSite X StandardTopology.fppf)
      (associatedRingedSite Y StandardTopology.fppf)
      (associatedTopology_hasSheafCompose X StandardTopology.fppf)
      (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
      (associatedRingedToposHom f StandardTopology.fppf))
#check (AlgebraicGeometry.AlgebraicStack.fppfModulePushforward_additive f :
  (fppfModulePushforward f).Additive)
#check (AlgebraicGeometry.AlgebraicStack.fppfHigherDirectImageFunctor f :
  ℕ → (fppfModules X ⥤ fppfModules Y))
#check (AlgebraicGeometry.AlgebraicStack.fppfHigherDirectImageFunctor_eq f :
  ∀ i : ℕ, fppfHigherDirectImageFunctor f i =
    @Functor.rightDerived _ _ _ _ _ _ _ (fppfModulePushforward f)
      (fppfModulePushforward_additive f) i)
#check (AlgebraicGeometry.AlgebraicStack.fppfHigherDirectImage f :
  fppfModules X → ℕ → fppfModules Y)
#check (AlgebraicGeometry.AlgebraicStack.fppfHigherDirectImage_eq f :
  ∀ (F : fppfModules X) (i : ℕ),
    fppfHigherDirectImage f F i = (fppfHigherDirectImageFunctor f i).obj F)

end ModuleAPI

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.GroupoidsOver

/-- Morphisms between algebraic stacks have small fppf sheaf sections, by
restricting the same presheaf to the étale topology and using its atlas certificate. -/
instance hasSmallAssociatedFppfTypeSections_of_algebraicStack {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    HasSmallAssociatedTypeSections f StandardTopology.fppf where
  small F Z := AlgebraicStack.EtaleSmallSections.sectionsSmall f
    ⟨F.obj, Presheaf.IsSheaf.of_le (etaleTopology_le_fppfTopology X) F.property⟩ Z.unop

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

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
      (hX : ∃ U : Over S, IsAffine U.left ∧ Nonempty (X ≌ GroupoidsOver.slice U)) (hY : ∃ U : Over S, IsAffine U.left ∧ Nonempty (Y ≌ GroupoidsOver.slice U))
      (i : ℕ) {F : fppfModules X} (hF : predicate X F) :
    predicate Y ((fppfHigherDirectImageFunctor f i).obj F)

namespace FppfModuleRule

/-- The maximal fppf-module rule, sending every algebraic stack to the full
category of fppf modules. -/
def max (S : Scheme.{u}) : FppfModuleRule S where
  predicate _ := ⊤
  isWeakSerre X := inferInstance
  mapsInverseImage_of_smooth := by intros; trivial
  mem_iff_of_smoothCovering := by
    intros
    constructor <;> intros <;> trivial
  mapsHigherDirectImage_of_affine := by intros; trivial

variable {S : Scheme.{u}} (M : FppfModuleRule S)

/-- Inverse image along a smooth morphism sends objects of the rule on the
target into the rule on the source. -/
theorem mapsInverseImage_obj {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f]
    {F : fppfModules Y} (hF : M.predicate Y F) :
    M.predicate X ((fppfModuleInverseImage f).obj F) :=
  M.mapsInverseImage_of_smooth f F hF

/-- Higher direct images in the fppf topology send objects of the rule into
the rule, when source and target are representable by affine schemes. -/
theorem mapsHigherDirectImage_of_affine_obj {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (hX : ∃ U : Over S, IsAffine U.left ∧ Nonempty (X ≌ GroupoidsOver.slice U)) (hY : ∃ U : Over S, IsAffine U.left ∧ Nonempty (Y ≌ GroupoidsOver.slice U))
    (i : ℕ) {F : fppfModules X} (hF : M.predicate X F) :
    M.predicate Y ((fppfHigherDirectImageFunctor f i).obj F) :=
  M.mapsHigherDirectImage_of_affine f hX hY i hF

end FppfModuleRule

end AlgebraicGeometry.AlgebraicStack
