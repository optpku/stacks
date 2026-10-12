/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Images
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import ReasLib.Algebra.Category.ModuleCat.Subobject
public import ReasLib.Algebra.Module.Submodule.Filtration
public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.ConvergenceRepresentatives
public import ReasLib.Order.Filtration

/-!
# Filtered Differential Modules as Filtered Differential Objects

This file gives the canonical `ModuleCat` realization of a module with a decreasing submodule
filtration and a filtration-preserving square-zero endomorphism.  It also identifies the
categorical convergence predicates with their submodule representative formulas.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe uR uM

namespace ModuleCat.SubmoduleFiltration

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/-- Package an antitone family of submodules as a filtered object of `ModuleCat R`. -/
@[stacks 012B "filtered ModuleCat object from submodules"]
noncomputable def object (F : ℤ → Submodule R M) (hF : Antitone F) :
    CategoryTheory.FilteredObject (ModuleCat.{uM} R) where
  obj := ModuleCat.of R M
  filtration :=
    { toFun := fun p ↦ (ModuleCat.subobjectModule (ModuleCat.of R M)).symm
          (F (OrderDual.ofDual p))
      monotone' := fun _ _ hpq ↦
        (ModuleCat.subobjectModule (ModuleCat.of R M)).symm.monotone (hF hpq) }

/-- Taking the submodule represented by a stage of `object F hF` recovers `F`. -/
@[simp]
theorem subobjectModule_stage (F : ℤ → Submodule R M) (hF : Antitone F) (p : ℤ) :
    ModuleCat.subobjectModule (ModuleCat.of R M) ((object F hF).filtration.stage p) =
      F p := sorry

end ModuleCat.SubmoduleFiltration

namespace ModuleCat.FilteredDifferentialObject

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/-- A linear endomorphism preserving a submodule factors through the corresponding canonical
`ModuleCat` subobject. -/
theorem factors_stage (d : M →ₗ[R] M) {S : Submodule R M}
    (hS : Submodule.map d S ≤ S) :
    ((ModuleCat.subobjectModule (ModuleCat.of R M)).symm S).Factors
      (((ModuleCat.subobjectModule (ModuleCat.of R M)).symm S).arrow ≫ ModuleCat.ofHom d) :=
  sorry

/-- A filtration-preserving linear endomorphism as an endomorphism of the corresponding filtered
object. -/
@[stacks 012B "filtered differential-module endomorphism"]
noncomputable def endomorphism (d : M →ₗ[R] M) (F : ℤ → Submodule R M)
    (hF : Antitone F) (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) :
    ModuleCat.SubmoduleFiltration.object F hF ⟶
      ModuleCat.SubmoduleFiltration.object F hF where
  hom := ModuleCat.ofHom d
  preserves p := factors_stage d (hdF p)

/-- The underlying linear map of the filtered endomorphism is the original map. -/
@[simp]
theorem endomorphism_hom (d : M →ₗ[R] M) (F : ℤ → Submodule R M)
    (hF : Antitone F) (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) :
    (endomorphism d F hF hdF).hom = ModuleCat.ofHom d := sorry

/-- A square-zero linear endomorphism remains square-zero after packaging as a filtered
endomorphism. -/
theorem endomorphism_comp_self_eq_zero (d : M →ₗ[R] M)
    (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) (hd : d.comp d = 0) :
    endomorphism d F hF hdF ≫ endomorphism d F hF hdF = 0 := sorry

/-- The reflexive complex shape on `PUnit` relates its unique pair of indices. -/
theorem reflPUnit_rel (i j : PUnit.{1}) : (ComplexShape.refl PUnit.{1}).Rel i j := sorry

/-- Package a filtered module with a filtration-preserving square-zero endomorphism as a
one-object filtered homological complex. -/
@[stacks 012B "filtered differential module as a filtered differential object"]
noncomputable def ofLinearMap (d : M →ₗ[R] M) (F : ℤ → Submodule R M)
    (hF : Antitone F) (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p)
    (hd : d.comp d = 0) :
    HomologicalComplex (CategoryTheory.FilteredObject (ModuleCat.{uM} R))
      (ComplexShape.refl PUnit.{1}) where
  X := fun _ ↦ ModuleCat.SubmoduleFiltration.object F hF
  d := fun _ _ ↦ endomorphism d F hF hdF
  shape := fun i j hij ↦ (hij (reflPUnit_rel i j)).elim
  d_comp_d' := fun _ _ _ _ _ ↦ endomorphism_comp_self_eq_zero d F hF hdF hd

/-- The unique object of `ofLinearMap d F hF hdF hd` is the filtered module built from `F`. -/
@[simp]
theorem ofLinearMap_X (d : M →ₗ[R] M) (F : ℤ → Submodule R M)
    (hF : Antitone F) (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p)
    (hd : d.comp d = 0) :
    (ofLinearMap d F hF hdF hd).X PUnit.unit =
      ModuleCat.SubmoduleFiltration.object F hF := sorry

/-- The differential of `ofLinearMap d F hF hdF hd` has underlying linear map `d`. -/
@[simp]
theorem ofLinearMap_d_hom (d : M →ₗ[R] M) (F : ℤ → Submodule R M)
    (hF : Antitone F) (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p)
    (hd : d.comp d = 0) :
    ((ofLinearMap d F hF hdF hd).d PUnit.unit PUnit.unit).hom = ModuleCat.ofHom d := sorry

namespace Homology.Convergence

/-- Weak convergence of the packaged filtered differential object is the submodule
representative criterion. -/
@[stacks 012J "ModuleCat weak convergence representative criterion"]
theorem isWeak_iff (d : M →ₗ[R] M)
    (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) (hd : d.comp d = 0) :
    HomologicalComplex.Filtered.Homology.Convergence.IsWeak
        (ofLinearMap d F hF hdF hd) ↔
      Submodule.FilteredLinearMap.weakConvergenceCriterion d F := sorry

end Homology.Convergence

namespace Homology.Filtration

/-- The categorical representative criterion for the packaged object is the corresponding
submodule subquotient-filtration criterion. -/
theorem criterion_iff (d : M →ₗ[R] M)
    (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) (hd : d.comp d = 0) :
    HomologicalComplex.Filtered.Homology.Filtration.criterion
        (ofLinearMap d F hF hdF hd) ↔
      Order.Filtration.Subquotient.IsSeparatedExhaustive F
        (LinearMap.range d) (LinearMap.ker d) := sorry

end Homology.Filtration

namespace Homology.Convergence

/-- Abutment of the packaged filtered differential object is weak convergence together with the
submodule representative criterion for its induced homology filtration. -/
@[stacks 012J "ModuleCat abutment representative criterion"]
theorem abuts_iff (d : M →ₗ[R] M) (F : ℤ → Submodule R M)
    (hF : Antitone F) (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p)
    (hd : d.comp d = 0) :
    HomologicalComplex.Filtered.Homology.Convergence.Abuts
        (ofLinearMap d F hF hdF hd) ↔
      Submodule.FilteredLinearMap.weakConvergenceCriterion d F ∧
        Order.Filtration.Subquotient.IsSeparatedExhaustive F
          (LinearMap.range d) (LinearMap.ker d) := sorry

end Homology.Convergence

end ModuleCat.FilteredDifferentialObject
