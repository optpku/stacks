module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Local free generators and their kernel relations

Sheafify the pointwise free module on the underlying local sections. The native adjunction
counit is epic because its right adjoint is faithful. Covering its kernel gives a displayed
cokernel presentation. The construction retains the coefficient universe even on a larger site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace SheafOfModules.LocalPresentation

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The native free-presheaf/sheafification adjunction. -/
def coverAdjunction :=
  (PresheafOfModules.freeAdjunction R.obj).comp
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj))

/-- Sheafification of the pointwise free module on all local sections. -/
def cover (M : SheafOfModules.{w} R) : SheafOfModules.{w} R :=
  (PresheafOfModules.free R.obj ⋙ PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj) ⋙
      PresheafOfModules.toPresheaf R.obj ⋙
      (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat)).obj M)

/-- The actual generator evaluation, given by the native composite counit. -/
def coverπ (M : SheafOfModules.{w} R) : cover M ⟶ M :=
  (coverAdjunction (R := R)).counit.app M

/-- Epimorphy follows from the faithful forgetful right adjoint. -/
instance coverπ_epi (M : SheafOfModules.{w} R) : Epi (coverπ M) := by
  exact (coverAdjunction (R := R)).counit_epi_of_R_faithful M

/-- Cover the actual kernel and include it into the generator sheaf. -/
def relation (M : SheafOfModules.{w} R) :
    cover (kernel (coverπ M)) ⟶ cover M :=
  coverπ (kernel (coverπ M)) ≫ kernel.ι (coverπ M)

/-- The first relation is the evaluation of the kernel followed by its inclusion. -/
theorem relation_comp_coverπ (M : SheafOfModules.{w} R) :
    relation M ≫ coverπ M = 0 := by
  simp only [relation, Category.assoc, kernel.condition, comp_zero]

/-- The displayed first relation and evaluation form a presentation cokernel. -/
def presentationIsColimit (M : SheafOfModules.{w} R) :
    IsColimit (CokernelCofork.ofπ (coverπ M) (relation_comp_coverπ M)) := by
  let S := ShortComplex.mk (relation M) (coverπ M) (relation_comp_coverπ M)
  let T := ShortComplex.mk (kernel.ι (coverπ M)) (coverπ M) (kernel.condition _)
  let φ : S ⟶ T :=
    { τ₁ := coverπ (kernel (coverπ M))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  exact ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    (T.exact_of_f_is_kernel (kernelIsKernel _))).gIsCokernel

end SheafOfModules.LocalPresentation
