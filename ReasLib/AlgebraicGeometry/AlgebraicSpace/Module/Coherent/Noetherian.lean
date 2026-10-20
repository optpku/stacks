/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subobject.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank

/-!
# Coherent modules on locally Noetherian algebraic spaces

On a locally Noetherian algebraic space, coherence of an `𝒪_X`-module is equivalent to
quasi-coherence of finite type, finite presentation, and coherence after étale pullback from a
scheme. The structure module, invertible modules, and finite locally free modules are coherent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]

/-- On a locally Noetherian algebraic space, a module sheaf is coherent iff it is quasi-coherent
and of finite type. -/
theorem isCoherent_iff_isQuasicoherent_and_isFiniteType (F : X.Modules) :
    F.IsCoherent ↔ F.IsQuasicoherent ∧ F.IsFiniteType :=
  sorry

/-- On a locally Noetherian algebraic space, coherence is equivalent to finite presentation. -/
theorem isCoherent_iff_isFinitePresentation (F : X.Modules) :
    F.IsCoherent ↔ F.IsFinitePresentation :=
  sorry

/-- Coherence is equivalent to coherence of every pullback along an étale morphism from a
scheme. -/
theorem isCoherent_iff_forall_etale (F : X.Modules) :
    F.IsCoherent ↔
      ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ], ((pullback φ).obj F).IsCoherent :=
  sorry

/-- Coherence is equivalent to coherence of the pullback along some surjective étale morphism
from a scheme. -/
theorem isCoherent_iff_exists_surjectiveEtale (F : X.Modules) :
    F.IsCoherent ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X),
        Etale φ ∧ Surjective φ ∧ ((pullback φ).obj F).IsCoherent :=
  sorry

/-- Coherence is equivalent to coherence of every pullback along a structural morphism of the
small étale site. -/
theorem isCoherent_iff_forall_smallEtale (F : X.Modules) :
    F.IsCoherent ↔ ∀ U : smallEtaleSite X, ((pullback U.hom).obj F).IsCoherent :=
  sorry

/-- A finite locally free module on a locally Noetherian algebraic space is coherent. -/
theorem isCoherent_of_isFiniteLocallyFree (F : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree F] : F.IsCoherent :=
  (isCoherent_iff_isFinitePresentation F).mpr inferInstance

/-- Finite locally free modules on a locally Noetherian algebraic space are canonically
coherent. -/
instance instIsCoherentOfIsFiniteLocallyFree (F : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree F] : F.IsCoherent :=
  isCoherent_of_isFiniteLocallyFree F

/-- A module of fixed finite local rank on a locally Noetherian algebraic space is coherent. -/
theorem isCoherent_of_isFiniteLocallyFreeOfRank (r : ℕ) (F : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r F] : F.IsCoherent :=
  isCoherent_of_isFiniteLocallyFree F

/-- An invertible module, encoded as finite locally free of rank one, is coherent on a locally
Noetherian algebraic space. -/
theorem isCoherent_of_isInvertible (L : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank 1 L] : L.IsCoherent :=
  isCoherent_of_isFiniteLocallyFreeOfRank 1 L

/-- Invertible modules on a locally Noetherian algebraic space are canonically coherent. -/
instance instIsCoherentOfIsInvertible (L : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank 1 L] : L.IsCoherent :=
  isCoherent_of_isInvertible L

/-- The structure module of a locally Noetherian algebraic space is coherent. -/
theorem structureSheaf_isCoherent (X : AlgebraicSpace S) [IsLocallyNoetherian X] :
    (SheafOfModules.unit (structureSheaf X) : X.Modules).IsCoherent :=
  isCoherent_of_isFiniteLocallyFree (SheafOfModules.unit (structureSheaf X))

/-- The structure module of a locally Noetherian algebraic space is canonically coherent. -/
instance instIsCoherentUnit (X : AlgebraicSpace S) [IsLocallyNoetherian X] :
    (SheafOfModules.unit (structureSheaf X) : X.Modules).IsCoherent :=
  structureSheaf_isCoherent X

/-- Every monotone natural-number-indexed chain of quasi-coherent subobjects of a coherent
module on a Noetherian algebraic space is eventually constant. -/
theorem quasiCoherentSubobject_monotone_stabilizes
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (F : X.Modules) [F.IsCoherent]
    (f : ℕ →o Subobject F)
    (hf_qc : ∀ n : ℕ, (((f n : Subobject F) : X.Modules)).IsQuasicoherent) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → f n = f m := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
