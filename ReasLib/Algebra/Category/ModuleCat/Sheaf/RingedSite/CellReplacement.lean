module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CellReplacement
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Homology.CochainComplex.KFlat

/-!
# Displayed cell models for complexes of sheaves of modules

The presheaf tower retains the original input and the augmentation given by the local cell
coordinates. Sheafification carries its actual terms, differentials and augmentation to sheaves.
Its increasing stage filtration attaches free cells with no new-component differential, which
is the filtration used to establish K-flatness over a commutative ring sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w uC vC

namespace SheafOfModules.CellReplacement

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (K : CochainComplex (SheafOfModules.{w} R) ℤ)

/-- The original underlying presheaf complex. -/
def underlying : CochainComplex (PresheafOfModules.{w} R.obj) ℤ :=
  ((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- The original attaching tower, built from the local cycle and boundary coordinates. -/
def presheafModel : CochainComplex (PresheafOfModules.{w} R.obj) ℤ :=
  PresheafOfModules.CellReplacement.replacement (underlying K)

/-- Its specified presheaf augmentation to the original input. -/
def presheafAugmentation : presheafModel K ⟶ underlying K :=
  PresheafOfModules.CellReplacement.augmentation (underlying K)

/-- An actual sheafified term of the displayed tower's colimit. -/
def modelTerm (n : ℤ) : SheafOfModules.{w} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj ((presheafModel K).X n)

/-- The differential is the sheafification of the original attaching differential. -/
def modelDifferential (n : ℤ) : modelTerm K n ⟶ modelTerm K (n + 1) :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map ((presheafModel K).d n (n + 1))

/-- Sheafification preserves the square-zero equation of the specified differential. -/
theorem modelDifferential_sq (n : ℤ) :
    modelDifferential K n ≫ modelDifferential K (n + 1) = 0 := sorry

/-- The actual global sheaf complex. -/
def model : CochainComplex (SheafOfModules.{w} R) ℤ :=
  CochainComplex.of (modelTerm K) (modelDifferential K) (modelDifferential_sq K)

/-- Each augmentation component is adjoint to the specified presheaf augmentation. -/
def augmentationTerm (n : ℤ) : modelTerm K n ⟶ K.X n :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
    ((presheafModel K).X n) (K.X n)).symm ((presheafAugmentation K).f n)

/-- The actual augmentation to the original input complex. -/
def augmentation : model K ⟶ K where
  f := augmentationTerm K
  comm' := sorry

/-- The adjunction recovers the original presheaf map on every term. -/
theorem augmentationTerm_adjoint (n : ℤ) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
      ((presheafModel K).X n) (K.X n) (augmentationTerm K n) =
      (presheafAugmentation K).f n := Equiv.apply_symm_apply _ _

/-- Exact sheafification carries the specified cell augmentation to a quasi-isomorphism. -/
@[stacks 06YS "displayed cell augmentation"]
theorem augmentation_quasiIso [HasSheafify J AddCommGrpCat.{w}] :
    QuasiIso (augmentation K) := sorry

/-- Sheafify an actual finite stage, retaining its original differential and augmentation. -/
def stage (s : ℕ) : CochainComplex (SheafOfModules.{w} R) ℤ :=
  ((PresheafOfModules.sheafification (𝟙 R.obj)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (PresheafOfModules.CellReplacement.stage (underlying K) s).complex

/-- The stage inclusion is the sheafification of the actual old-summand inclusion. -/
def stageMap (s : ℕ) : stage K s ⟶ stage K (s + 1) :=
  ((PresheafOfModules.sheafification (𝟙 R.obj)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map (PresheafOfModules.CellReplacement.transition (underlying K) s)

end SheafOfModules.CellReplacement

namespace SheafOfModules.RingedSite.CellReplacement

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}}
variable (K : CochainComplex (ringedSiteModuleCategory.{uC, vC, w, w} J O) ℤ)

/-- Every stage term is flat: it is a finite iterative direct sum of the sheafified free cells.
The statement uses the canonical tensor structure over the commutative ring sheaf. -/
theorem stage_termwiseFlat (s : ℕ) :
    HomologicalComplex.IsTermwiseFlat (SheafOfModules.CellReplacement.stage K s) := sorry

/-- Each stage is K-flat. Its attaching filtration has zero-differential quotients consisting
of shifted flat free-cell sheaves; the differential of a new cell lands in the previous stage. -/
theorem stage_isKFlat (s : ℕ) :
    (SheafOfModules.CellReplacement.stage K s).IsKFlat := sorry

/-- The displayed cell model is termwise flat: its terms are the filtered colimits of the
flat stage terms under the specified split inclusions. -/
@[stacks 06YS "displayed flat-term model"]
theorem model_termwiseFlat :
    HomologicalComplex.IsTermwiseFlat (SheafOfModules.CellReplacement.model K) := sorry

/-- The increasing displayed filtration makes the actual model K-flat. Filtered colimits
commute with the tensor totalizations and are exact on module sheaves. -/
@[stacks 06YS "displayed K-flat model"]
theorem model_isKFlat :
    (SheafOfModules.CellReplacement.model K).IsKFlat := sorry

end SheafOfModules.RingedSite.CellReplacement
