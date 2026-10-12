/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Data.PNat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
public import stacks_project.Chap61.Lemma_61_19_8_Comparison
public import stacks_project.Chap61.Lemma_61_19_11_Reduction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.19.11

If the reduction `K_1` of `K` in `D(X.ProEt, Λ)` lies in the essential image of
derived `ε⁻¹` and has Tor-amplitude in `[a, ∞)`, then both properties pass to
every positive-power reduction `K_n` in `D(X.ProEt, Λ ⧸ I ^ n)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open ComplexShape
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]
variable (I : Ideal Λ)
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I)))]
variable [MonoidalCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I)))]

-- Local declaration justification (instance diamond): `Sheaf` is a `FullSubcategory`,
-- so `HasZeroMorphisms`/`Preadditive` are synthesized from that embedding, while
-- derived tensor is typed using `Abelian.toPreadditive`.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory
attribute [-instance] Preadditive.fullSubcategory

variable [MonoidalPreadditive (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I)))]
variable [∀ (K L : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I))) ℤ),
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I))))
    (ComplexShape.up ℤ)]
variable [h_derivedTensor :
  @DerivedTensor.Right.Has (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I)))
    _ _ _ _ _ _]
variable [(proEtModuleExtendScalars (Ideal.Quotient.mk I) X).Additive]
variable [(Functor.Homotopy.toDerived
    (proEtModuleExtendScalars (Ideal.Quotient.mk I) X)).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso
    (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (up ℤ))]

/-- Lemma 61.19.11 (1): for a scheme `X`, a Noetherian ring `Λ`, an ideal `I ⊆ Λ`,
and `K` in `D(X.ProEt, Λ)`, if the reduction of `K` modulo `I` lies in the essential
image of derived `ε⁻¹ : D(X.Etale, Λ ⧸ I) ⥤ D(X.ProEt, Λ ⧸ I)` and has
Tor-amplitude in `[a, ∞)`, then every positive-power reduction `K_n` lies in the
essential image of derived `ε⁻¹` on `D(X.ProEt, Λ ⧸ I ^ n)`. -/
@[stacks 09B2]
theorem proEtReduction_mem_essImage
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I)))]
    [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I),
      (etaleToProEt X).op.HasLeftKanExtension F]
    [(etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I))).Additive]
    [PreservesFiniteLimits (etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I)))]
    [PreservesFiniteColimits (etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I)))]
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))) (a : ℤ)
    (h_ess :
      (etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I))).mapDerivedCategory.essImage
        ((proEtDerivedExtendScalars (Ideal.Quotient.mk I) X).obj K))
    (h_tor : DerivedTensor.HasTorAmplitudeGE
      ((proEtDerivedExtendScalars (Ideal.Quotient.mk I) X).obj K) a) (n : ℕ+)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [HasDerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [HasDerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)),
      (etaleToProEt X).op.HasLeftKanExtension F]
    [(etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))).Additive]
    [PreservesFiniteLimits
      (etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [PreservesFiniteColimits
      (etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (up ℤ))] :
    (etaleToProEtPullback X
        (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))).mapDerivedCategory.essImage
      (proEtReduction I n K) :=
  sorry

/-- Lemma 61.19.11 (2): for a scheme `X`, a Noetherian ring `Λ`, an ideal `I ⊆ Λ`,
and `K` in `D(X.ProEt, Λ)`, if the reduction of `K` modulo `I` has Tor-amplitude
in `[a, ∞)`, then every positive-power reduction `K_n` has the same Tor-amplitude
bound in `D(X.ProEt, Λ ⧸ I ^ n)`. -/
@[stacks 09B2]
theorem proEtReduction_hasTorAmplitudeGE
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))) (a : ℤ)
    (h_tor : DerivedTensor.HasTorAmplitudeGE
      ((proEtDerivedExtendScalars (Ideal.Quotient.mk I) X).obj K) a) (n : ℕ+)
    [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [HasDerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (up ℤ))]
    [MonoidalCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [MonoidalPreadditive
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [∀ (K L : CochainComplex
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (curriedTensor
          (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))))
        (ComplexShape.up ℤ)]
    [h_derivedTensor_n :
      @DerivedTensor.Right.Has
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))
        _ _ _ _ _ _] :
    DerivedTensor.HasTorAmplitudeGE (proEtReduction I n K) a :=
  sorry

end AlgebraicGeometry.Scheme

end

end
