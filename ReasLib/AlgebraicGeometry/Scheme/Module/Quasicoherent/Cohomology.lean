/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AffinePushforward
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Effaceable

/-!
# Cohomology of quasicoherent modules

This module records global cohomology on the category of quasicoherent modules, the property of
having vanishing positive-degree global cohomology, and the resulting effaceability and
universality statements.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- The degree-`n` global cohomology functor on quasicoherent modules over a scheme. -/
noncomputable abbrev globalCohomologyFunctor (X : Scheme.{u}) (n : ℕ) :
    QCoh X ⥤ AddCommGrpCat :=
  inclusion X ⋙
    SheafOfModules.toSheaf X.ringCatSheaf ⋙
      Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X.carrier) n ⋙
        (CategoryTheory.evaluation ((Opens X)ᵒᵖ) AddCommGrpCat).obj (op (⊤ : Opens X))

/-- A quasicoherent module is globally cohomologically acyclic when all of its positive-degree
global cohomology objects vanish. -/
def globalCohomologyAcyclic (X : Scheme.{u}) : ObjectProperty (QCoh X) :=
  fun F ↦ ∀ p : ℕ, 0 < p → IsZero ((globalCohomologyFunctor X p).obj F)

variable {X : Scheme.{u}}

/-- On a quasi-compact scheme with affine diagonal, every quasicoherent module embeds into a
globally cohomologically acyclic quasicoherent module. -/
theorem exists_mono_to_globalCohomologyAcyclic
    [CompactSpace X.carrier] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (F : QCoh X) :
    ∃ (F' : QCoh X) (i : F ⟶ F'), Mono i ∧ globalCohomologyAcyclic X F' := sorry

/-- On a quasi-compact scheme with affine diagonal, globally cohomologically acyclic modules
provide monomorphic embeddings for all quasicoherent modules. -/
instance globalCohomologyAcyclic_hasMonoEmbedding
    (X : Scheme.{u}) [CompactSpace X.carrier] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))] :
    (globalCohomologyAcyclic X).HasMonoEmbedding := sorry

/-- Positive-degree global cohomology on quasicoherent modules is effaceable on a quasi-compact
scheme with affine diagonal. -/
theorem globalCohomologyFunctor_isEffaceable
    (X : Scheme.{u}) [CompactSpace X.carrier] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (n : ℕ) (hn : 0 < n) :
    (globalCohomologyFunctor X n).IsEffaceable := sorry

/-- On a quasi-compact scheme with affine diagonal, the degreewise global cohomology functors on
quasicoherent modules underlie a universal cohomological delta functor. -/
theorem exists_universal_globalCohomology_deltaFunctor
    (X : Scheme.{u}) [CompactSpace X.carrier] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))] :
    ∃ T : CohomologicalDeltaFunctor (QCoh X) AddCommGrpCat,
      (∀ n : ℕ, (T.F n).obj = globalCohomologyFunctor X n) ∧ T.IsUniversal := sorry

end AlgebraicGeometry.Scheme.QCoh
