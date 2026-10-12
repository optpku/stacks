/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap69.Definition_69_12_1_Instances

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

/-- The structure module of a locally Noetherian algebraic space is coherent. -/
theorem structureSheaf_isCoherent (X : AlgebraicSpace S) [IsLocallyNoetherian X] :
    (SheafOfModules.unit (structureSheaf X) : X.Modules).IsCoherent :=
  sorry

/-- The structure module of a locally Noetherian algebraic space is canonically coherent. -/
instance instIsCoherentUnit (X : AlgebraicSpace S) [IsLocallyNoetherian X] :
    (SheafOfModules.unit (structureSheaf X) : X.Modules).IsCoherent :=
  sorry

/-- A finite locally free module on a locally Noetherian algebraic space is coherent. -/
theorem isCoherent_of_isFiniteLocallyFree (F : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree F] : F.IsCoherent :=
  sorry

/-- Finite locally free modules on a locally Noetherian algebraic space are canonically
coherent. -/
instance instIsCoherentOfIsFiniteLocallyFree (F : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree F] : F.IsCoherent :=
  sorry

/-- A module of fixed finite local rank on a locally Noetherian algebraic space is coherent. -/
theorem isCoherent_of_isFiniteLocallyFreeOfRank (r : ℕ) (F : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r F] : F.IsCoherent :=
  sorry

/-- An invertible module, encoded as finite locally free of rank one, is coherent on a locally
Noetherian algebraic space. -/
theorem isCoherent_of_isInvertible (L : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank 1 L] : L.IsCoherent :=
  sorry

/-- Invertible modules on a locally Noetherian algebraic space are canonically coherent. -/
instance instIsCoherentOfIsInvertible (L : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank 1 L] : L.IsCoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
