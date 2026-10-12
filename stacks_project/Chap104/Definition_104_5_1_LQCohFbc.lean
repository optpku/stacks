/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.CategoryTheory.Sites.MorphismOfSites.Topology
public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import stacks_project.Chap96.Lemma_96_12_4_LQCoh
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap103.Definition_103_7_1_FlatBaseChange
public import stacks_project.Chap103.Definition_103_9_1_Parasitic

/-!
# Locally quasi-coherent modules with flat base change

`LQCoh^{fbc}` is first the full subcategory of étale `𝒪_X`-modules that are
locally quasi-coherent and have the flat base change property. The same class
is transported to `Mod(𝒪_X) = Mod(X_fppf, 𝒪_X)` along the identity-on-objects
restriction from the fppf topology to the étale topology. Parasitic modules on
the fppf site are those whose underlying presheaf vanishes on objects whose
2-Yoneda morphism is a flat morphism of algebraic stacks.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open FiberedCategoryOver.Groupoids Functor.Fiber Opposite Limits
open RingedSite.Hom
open scoped Bicategory ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The object property of étale `𝒪_X`-modules that are locally quasi-coherent
and have the flat base change property. -/
abbrev lqcohFbc (X : GroupoidsOver S) [AlgebraicStack X] :
    ObjectProperty (etaleModules X) :=
  locallyQuasiCoherent X ⊓ hasFlatBaseChange X

/-- Membership in `lqcohFbc` is local quasi-coherence together with the flat
base change property. -/
theorem lqcohFbc_iff {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) :
    lqcohFbc X F ↔ IsLocallyQuasiCoherent F ∧ HasFlatBaseChange F := sorry

/-- `lqcohFbc` is the infimum of local quasi-coherence and flat base change. -/
theorem lqcohFbc_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    lqcohFbc X = locallyQuasiCoherent X ⊓ hasFlatBaseChange X := sorry

/-- Locally quasi-coherent étale `𝒪_X`-modules with the flat base change
property form a weak Serre class. -/
instance lqcohFbc_isWeakSerreClass (X : GroupoidsOver S) [AlgebraicStack X] :
    IsWeakSerreClass (lqcohFbc X) := sorry

/-- The category of locally quasi-coherent étale `𝒪_X`-modules with the flat
base change property. -/
abbrev LQCohFbc (X : GroupoidsOver S) [AlgebraicStack X] :=
  (lqcohFbc X).FullSubcategory

namespace LQCohFbc

/-- The inclusion of étale `LQCoh^{fbc}(𝒪_X)` into étale `𝒪_X`-modules. -/
abbrev inclusion (X : GroupoidsOver S) [AlgebraicStack X] :
    LQCohFbc X ⥤ etaleModules X :=
  (lqcohFbc X).ι

/-- The inclusion of `LQCohFbc X` is the full-subcategory inclusion of
`lqcohFbc X`. -/
theorem inclusion_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    inclusion X = (lqcohFbc X).ι := sorry

end LQCohFbc

namespace EtaleModules

/-- An étale `𝒪_X`-module is parasitic if it vanishes on every object `x` of
`X` lying over a scheme `U` whose 2-Yoneda morphism `U ⟶ X` is a flat morphism
of algebraic stacks. -/
@[mk_iff]
class IsParasitic {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) : Prop where
  /-- The value `F(x)` is the zero module whenever `x : U ⟶ X` is flat. -/
  isZero_of_flat : ∀ {U : Over S} (x : X.p.Fiber U),
    AlgebraicStack.Flat (YonedaSlice.representative x) →
      IsZero (F.val.obj (op (fiberInclusion.obj x)))

/-- Source-semantic characterisation: `F` is parasitic if and only if `F(x) = 0`
whenever the 2-Yoneda morphism of `x` is a flat morphism of algebraic stacks. -/
theorem isParasitic_spec {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) :
    IsParasitic F ↔
      ∀ {U : Over S} (x : X.p.Fiber U),
        AlgebraicStack.Flat (YonedaSlice.representative x) →
          IsZero (F.val.obj (op (fiberInclusion.obj x))) := sorry

/-- A parasitic étale `𝒪_X`-module vanishes on a specified object whose
2-Yoneda morphism is flat. -/
theorem IsParasitic.isZero {X : GroupoidsOver S} [AlgebraicStack X]
    {F : etaleModules X} [IsParasitic F] {U : Over S} (x : X.p.Fiber U)
    (hx : AlgebraicStack.Flat (YonedaSlice.representative x)) :
    IsZero (F.val.obj (op (fiberInclusion.obj x))) := sorry

/-- The zero étale `𝒪_X`-module is parasitic. -/
instance instIsParasitic_of_isZero {X : GroupoidsOver S} [AlgebraicStack X] :
    IsParasitic (0 : etaleModules X) := sorry

/-- A zero object in `Mod(X_étale, 𝒪_X)` is parasitic. -/
theorem isParasitic_of_isZero {X : GroupoidsOver S} [AlgebraicStack X]
    {F : etaleModules X} (hF : IsZero F) : IsParasitic F := sorry

/-- The object property of parasitic étale `𝒪_X`-modules. -/
abbrev parasitic (X : GroupoidsOver S) [AlgebraicStack X] :
    ObjectProperty (etaleModules X) :=
  IsParasitic

/-- Membership in `parasitic X` is the class `IsParasitic`. -/
theorem mem_parasitic {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) :
    parasitic X F ↔ IsParasitic F := sorry

/-- Parasitic étale `𝒪_X`-modules form a weak Serre class. -/
instance parasitic_isWeakSerreClass (X : GroupoidsOver S) [AlgebraicStack X] :
    IsWeakSerreClass (parasitic X) := sorry

end EtaleModules

/-- The object property of parasitic locally quasi-coherent étale `𝒪_X`-modules
with the flat base change property. -/
abbrev parasiticLQCohFbc (X : GroupoidsOver S) [AlgebraicStack X] :
    ObjectProperty (etaleModules X) :=
  EtaleModules.parasitic X ⊓ lqcohFbc X

/-- Membership in `parasiticLQCohFbc` is parasitic vanishing together with
local quasi-coherence and the flat base change property. -/
theorem parasiticLQCohFbc_iff {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) :
    parasiticLQCohFbc X F ↔
      EtaleModules.IsParasitic F ∧ IsLocallyQuasiCoherent F ∧
        HasFlatBaseChange F := sorry

/-- `parasiticLQCohFbc` is the infimum of the parasitic property and
`lqcohFbc`. -/
theorem parasiticLQCohFbc_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    parasiticLQCohFbc X = EtaleModules.parasitic X ⊓ lqcohFbc X := sorry

/-- Parasitic objects of étale `LQCoh^{fbc}(𝒪_X)` form a weak Serre class. -/
instance parasiticLQCohFbc_isWeakSerreClass (X : GroupoidsOver S)
    [AlgebraicStack X] :
    IsWeakSerreClass (parasiticLQCohFbc X) := sorry

/-- The category of sheaves of modules on `(X_fppf, 𝒪_X)`. -/
abbrev fppfModules (X : GroupoidsOver S) :=
  RingedSite.ModuleCat.{u} (fppfRingedSite X)

/-- `fppfModules X` is the module category of the fppf ringed site of `X`. -/
theorem fppfModules_eq (X : GroupoidsOver S) :
    fppfModules X = RingedSite.ModuleCat.{u} (fppfRingedSite X) := sorry

/-- The category of fppf `𝒪_X`-modules is abelian. -/
instance fppfModulesAbelian (X : GroupoidsOver S) : Abelian (fppfModules X) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

/-- The associated étale topology is coarser than the fppf topology of the
ringed site of `X`. -/
theorem etaleTopology_le_fppf (X : GroupoidsOver S) :
    (etaleRingedSite X).siteTopology ≤ (fppfRingedSite X).siteTopology := sorry

/-- The identity functor is continuous from the étale topology to the fppf
topology of `X`. -/
instance instEtaleIdIsContinuousFppf (X : GroupoidsOver S) :
    (𝟭 X.total).IsContinuous
      (etaleRingedSite X).siteTopology (fppfRingedSite X).siteTopology :=
  Functor.id_isContinuous_of_le (etaleTopology_le_fppf X)

/-- The identity functor is a morphism of sites `X_fppf → X_étale`. -/
instance instEtaleIdIsMorphismOfSites (X : GroupoidsOver S) :
    IsMorphismOfSites
      (etaleRingedSite X).siteTopology (fppfRingedSite X).siteTopology
      (𝟭 X.total) :=
  IsMorphismOfSites.id_of_le (etaleTopology_le_fppf X)

/-- Identity-on-sections comparison from the étale structure sheaf to the
direct image of the fppf structure sheaf. -/
def etaleToFppfStructureSheafMap (X : GroupoidsOver S) :
    (etaleRingedSite X).structureSheaf ⟶
      ((𝟭 X.total).sheafPushforwardContinuous RingCat.{u}
        (etaleRingedSite X).siteTopology
        (fppfRingedSite X).siteTopology).obj
        (fppfRingedSite X).structureSheaf :=
  Sheaf.homEquiv.symm
    { app := fun _ ↦ 𝟙 _
      naturality := fun _ _ _ ↦ sorry }

/-- The identity-on-objects morphism of ringed sites `X_fppf → X_étale`. -/
def etaleFppfHom (X : GroupoidsOver S) :
    RingedSite.Hom (fppfRingedSite X) (etaleRingedSite X) where
  base := 𝟭 X.total
  isMorphismOfSites := instEtaleIdIsMorphismOfSites X
  structureSheafMap := etaleToFppfStructureSheafMap X

/-- The base of `etaleFppfHom X` is the identity functor. -/
theorem etaleFppfHom_base (X : GroupoidsOver S) :
    (etaleFppfHom X).base = 𝟭 X.total := sorry

/-- Restriction of fppf `𝒪_X`-modules to étale `𝒪_X`-modules along the
identity-on-objects comparison of the two inherited topologies. -/
def restriction (X : GroupoidsOver S) :
    fppfModules X ⥤ etaleModules X :=
  (etaleFppfHom X).modulePushforward.{u}

/-- `restriction X` is module pushforward along `etaleFppfHom X`. -/
theorem restriction_eq (X : GroupoidsOver S) :
    restriction X = (etaleFppfHom X).modulePushforward.{u} := sorry

namespace FppfModules

/-- The object property of fppf `𝒪_X`-modules whose étale restriction lies in
`LQCoh^{fbc}`. -/
abbrev lqcohFbc (X : GroupoidsOver S) [AlgebraicStack X] :
    ObjectProperty (fppfModules X) :=
  (GroupoidsOver.lqcohFbc X).inverseImage (restriction X)

/-- An fppf module lies in `FppfModules.lqcohFbc` iff its étale restriction is
locally quasi-coherent and has the flat base change property. -/
theorem lqcohFbc_iff {X : GroupoidsOver S} [AlgebraicStack X]
    (F : fppfModules X) :
    lqcohFbc X F ↔
      IsLocallyQuasiCoherent ((restriction X).obj F) ∧
        HasFlatBaseChange ((restriction X).obj F) := sorry

/-- `FppfModules.lqcohFbc` is the inverse image of étale `lqcohFbc` along
`restriction`. -/
theorem lqcohFbc_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    lqcohFbc X = (GroupoidsOver.lqcohFbc X).inverseImage (restriction X) :=
  sorry

/-- Locally quasi-coherent fppf `𝒪_X`-modules with the flat base change
property form a weak Serre class. -/
instance lqcohFbc_isWeakSerreClass (X : GroupoidsOver S) [AlgebraicStack X] :
    IsWeakSerreClass (lqcohFbc X) := sorry

/-- The category of locally quasi-coherent fppf `𝒪_X`-modules with the flat
base change property. -/
abbrev LQCohFbc (X : GroupoidsOver S) [AlgebraicStack X] :=
  (lqcohFbc X).FullSubcategory

/-- The inclusion of fppf `LQCoh^{fbc}(𝒪_X)` into `Mod(𝒪_X)`. -/
abbrev inclusion (X : GroupoidsOver S) [AlgebraicStack X] :
    LQCohFbc X ⥤ fppfModules X :=
  (lqcohFbc X).ι

/-- The object property of parasitic fppf `𝒪_X`-modules, using the presheaf
vanishing condition of `IsParasitic`. -/
abbrev parasitic (X : GroupoidsOver S) [AlgebraicStack X] :
    ObjectProperty (fppfModules X) :=
  fun F ↦ IsParasitic F.val

/-- Membership in `FppfModules.parasitic` is parasitic vanishing of the
underlying fppf presheaf. -/
theorem mem_parasitic {X : GroupoidsOver S} [AlgebraicStack X]
    (F : fppfModules X) :
    parasitic X F ↔ IsParasitic F.val := sorry

/-- Source-semantic characterisation of parasitic fppf modules. -/
theorem isParasitic_spec {X : GroupoidsOver S} [AlgebraicStack X]
    (F : fppfModules X) :
    parasitic X F ↔
      ∀ {U : Over S} (x : X.p.Fiber U),
        AlgebraicStack.Flat (YonedaSlice.representative x) →
          IsZero (F.val.obj (op (fiberInclusion.obj x))) := sorry

/-- The zero fppf `𝒪_X`-module is parasitic. -/
theorem parasitic_zero (X : GroupoidsOver S) [AlgebraicStack X] :
    parasitic X (0 : fppfModules X) := sorry

/-- Parasitic fppf `𝒪_X`-modules form a weak Serre class. -/
instance parasitic_isWeakSerreClass (X : GroupoidsOver S) [AlgebraicStack X] :
    IsWeakSerreClass (parasitic X) := sorry

/-- The object property of parasitic objects of fppf `LQCoh^{fbc}(𝒪_X)`. -/
abbrev parasiticLQCohFbc (X : GroupoidsOver S) [AlgebraicStack X] :
    ObjectProperty (fppfModules X) :=
  parasitic X ⊓ lqcohFbc X

/-- Membership in `FppfModules.parasiticLQCohFbc` is parasitic vanishing
together with étale local quasi-coherence and flat base change of the
restriction. -/
theorem parasiticLQCohFbc_iff {X : GroupoidsOver S} [AlgebraicStack X]
    (F : fppfModules X) :
    parasiticLQCohFbc X F ↔
      IsParasitic F.val ∧
        IsLocallyQuasiCoherent ((restriction X).obj F) ∧
          HasFlatBaseChange ((restriction X).obj F) := sorry

/-- `FppfModules.parasiticLQCohFbc` is the infimum of the fppf parasitic
property and fppf `lqcohFbc`. -/
theorem parasiticLQCohFbc_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    parasiticLQCohFbc X = parasitic X ⊓ lqcohFbc X := sorry

/-- Parasitic objects of fppf `LQCoh^{fbc}(𝒪_X)` form a weak Serre class. -/
instance parasiticLQCohFbc_isWeakSerreClass (X : GroupoidsOver S)
    [AlgebraicStack X] :
    IsWeakSerreClass (parasiticLQCohFbc X) := sorry

end FppfModules

end AlgebraicGeometry.GroupoidsOver
