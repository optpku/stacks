/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed.Bifunctor
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.CategoryTheory.Monoidal.Adjunction.InternalHom
public import ReasLib.CategoryTheory.Monoidal.Functor.TensorComparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative RHom across extension and restriction of scalars

@stack 0E1W

This file specializes the internal-Hom comparison for a monoidal adjunction to
derived extension and restriction of scalars.  It keeps the tensor comparison
and the two coherent canonical-`RHom` presentations explicit.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.Restriction

variable {R S : Type u} [CommRing R] [CommRing S]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} R))]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} S))]
variable [RHom.Has (A := R)] [RHom.Has (A := S)]

/-- The canonical derived extension functor used by the relative `RHom` comparison. -/
@[stacks 0E1W "derived extension functor for relative RHom"]
noncomputable abbrev extension (σ : R →+* S) :=
  ModuleCat.derivedExtensionOfScalars.{u, u, u} σ

/-- The canonical derived restriction functor used by the relative `RHom` comparison. -/
@[stacks 0E1W "derived restriction functor for relative RHom"]
noncomputable abbrev restriction (σ : R →+* S) :=
  ModuleCat.derivedRestrictionOfScalars.{u} σ

/-- Lemma 15.100.1 (0E1W), functorial form: canonical `RHom` over `R`, after
restricting the target, is naturally isomorphic to restricted canonical `RHom`
over `S` after extending the source. -/
@[stacks 0E1W "Lemma 15.100.1 relative RHom natural isomorphism"]
noncomputable def comparisonNatIso
    (σ : R →+* S)
    (MR : RHom.BifunctorComparison (A := R))
    (MS : RHom.BifunctorComparison (A := S))
    (T : Functor.TensorComparison (extension σ))
    (K : DerivedCategory (ModuleCat.{u} R)) :
    restriction σ ⋙ RHom.At.targetFunctor (R := R) K ≅
      RHom.At.targetFunctor (R := S) ((extension σ).obj K) ⋙ restriction σ :=
  Functor.isoWhiskerLeft (restriction σ) (MR.targetIso K) ≪≫
    Adjunction.InternalHom.comparisonNatIso
      (ModuleCat.derivedExtensionRestrictionAdjunction σ)
      MR.closed MS.closed T K ≪≫
    Functor.isoWhiskerRight (MS.targetIso ((extension σ).obj K)).symm
      (restriction σ)

/-- Lemma 15.100.1 (0E1W): the objectwise canonical isomorphism
`RHom_R(K, Res M) ≅ Res (RHom_S(K ⊗ᴸ_R S, M))`. -/
@[stacks 0E1W "Lemma 15.100.1 relative RHom object isomorphism"]
noncomputable def comparisonIso
    (σ : R →+* S)
    (MR : RHom.BifunctorComparison (A := R))
    (MS : RHom.BifunctorComparison (A := S))
    (T : Functor.TensorComparison (extension σ))
    (K : DerivedCategory (ModuleCat.{u} R))
    (M : DerivedCategory (ModuleCat.{u} S)) :
    RHom.obj (A := R) K ((restriction σ).obj M) ≅
      (restriction σ).obj (RHom.obj (A := S) ((extension σ).obj K) M) :=
  (comparisonNatIso σ MR MS T K).app M

end CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.Restriction
