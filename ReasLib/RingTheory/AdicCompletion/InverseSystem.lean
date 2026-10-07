module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.InverseSystem.Positive.Cone
public import ReasLib.CategoryTheory.InverseSystem.Positive.ModuleCat.Limits
public import ReasLib.RingTheory.AdicCompletion.Completeness
public import ReasLib.RingTheory.AdicCompletion.QuotientSystem.Limits

/-!
# Adic Completion and Positive Inverse Systems

This leaf owns the comparison between an adic completion and the limit of a
positive inverse system.  It is organized around a compatible cone, so a
family of stage maps and its naturality are represented once by the standard
categorical object rather than repeated as separate hypotheses.

@stack 0G1Q
@stack 09B8
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u v

namespace CategoryTheory.PNatInverseSystem.Cone

variable {R : Type u} [CommRing R]
variable {F : PNatInverseSystem (ModuleCat.{v} R)}

/-- The map from the quotient of a cone vertex by `I ^ n` to the `n`th stage,
obtained by descending the cone stage map. -/
abbrev adicQuotientStageMap
    (s : Cone F) (I : Ideal R)
    (h_ker : ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule R s.pt) ≤
        LinearMap.ker (PNatInverseSystem.Cone.stageMap s n).hom)
    (n : ℕ+) :
    (s.pt ⧸ I ^ (n : ℕ) • (⊤ : Submodule R s.pt)) →ₗ[R] F.stage n :=
  (I ^ (n : ℕ) • (⊤ : Submodule R s.pt)).liftQ
    (PNatInverseSystem.Cone.stageMap s n).hom (h_ker n)

/-- The descended quotient-stage map recovers the original cone stage map on
representatives. -/
theorem adicQuotientStageMap_comp_mkQ
    (s : Cone F) (I : Ideal R)
    (h_ker : ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule R s.pt) ≤
        LinearMap.ker (PNatInverseSystem.Cone.stageMap s n).hom)
    (n : ℕ+) :
    (PNatInverseSystem.Cone.adicQuotientStageMap s I h_ker n).comp
        (Submodule.mkQ (I ^ (n : ℕ) • (⊤ : Submodule R s.pt))) =
      (PNatInverseSystem.Cone.stageMap s n).hom := sorry

/-- The kernel of a descended cone stage map is the image of the original
stage-map kernel in the corresponding quotient. -/
theorem ker_adicQuotientStageMap
    (s : Cone F) (I : Ideal R)
    (h_ker : ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule R s.pt) ≤
        LinearMap.ker (PNatInverseSystem.Cone.stageMap s n).hom)
    (n : ℕ+) :
    LinearMap.ker (PNatInverseSystem.Cone.adicQuotientStageMap s I h_ker n) =
      (LinearMap.ker (PNatInverseSystem.Cone.stageMap s n).hom).map
        (Submodule.mkQ (I ^ (n : ℕ) • (⊤ : Submodule R s.pt))) := sorry

/-- Stagewise annihilation by `I ^ n` implies that the `n`th cone stage map
kills `I ^ n` times its whole vertex. -/
theorem pow_smul_top_le_ker_stageMap_of_annihilated
    (s : Cone F) (I : Ideal R)
    (h_annihilated : ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule R (F.stage n)) = ⊥) :
    ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule R s.pt) ≤
        LinearMap.ker (PNatInverseSystem.Cone.stageMap s n).hom := sorry

/-- The natural transformation from the positive quotient system of a cone
vertex to the target system, obtained from all descended stage maps. -/
noncomputable def adicQuotientNatTrans
    (s : Cone F) (I : Ideal R)
    (h_ker : ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule R s.pt) ≤
        LinearMap.ker (PNatInverseSystem.Cone.stageMap s n).hom) :
    AdicCompletion.positiveQuotientSystem I s.pt ⟶ F where
  app i := ModuleCat.ofHom
    (PNatInverseSystem.Cone.adicQuotientStageMap s I h_ker (OrderDual.ofDual i))
  naturality := sorry

/-- The canonical comparison from the adic completion of a cone vertex to the
limit of the target positive inverse system. -/
noncomputable def adicCompletionComparison
    (s : Cone F) (I : Ideal R)
    (h_ker : ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule R s.pt) ≤
        LinearMap.ker (PNatInverseSystem.Cone.stageMap s n).hom)
    [HasLimit F] :
    ModuleCat.of R (AdicCompletion I s.pt) ⟶ (limit F : ModuleCat R) :=
  AdicCompletion.toLimit I s.pt
    (PNatInverseSystem.Cone.adicQuotientNatTrans s I h_ker)

/-- The cone-based completion comparison evaluates at stage `n` by first
taking the `n`th completion coordinate and then applying the descended cone
stage map. -/
theorem adicCompletionComparison_comp_limitProjection
    (s : Cone F) (I : Ideal R)
    (h_ker : ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule R s.pt) ≤
        LinearMap.ker (PNatInverseSystem.Cone.stageMap s n).hom)
    [HasLimit F] (n : ℕ+) :
    PNatInverseSystem.Cone.adicCompletionComparison s I h_ker ≫ F.limitProjection n =
      ModuleCat.ofHom
        ((PNatInverseSystem.Cone.adicQuotientStageMap s I h_ker n).comp
          (AdicCompletion.eval I s.pt (n : ℕ))) := sorry

/-- The completion-to-limit comparison specialized to a stagewise
annihilated positive inverse system. -/
noncomputable def adicCompletionComparisonOfAnnihilated
    (s : Cone F) (I : Ideal R)
    (h_annihilated : ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule R (F.stage n)) = ⊥)
    [HasLimit F] :
    ModuleCat.of R (AdicCompletion I s.pt) ⟶ limit F :=
  PNatInverseSystem.Cone.adicCompletionComparison s I
    (PNatInverseSystem.Cone.pow_smul_top_le_ker_stageMap_of_annihilated
      s I h_annihilated)

/-- The comparison from the tensor presentation of an adic completion to the
limit of a positive inverse system. -/
noncomputable def tensorToLimit
    {G : PNatInverseSystem (ModuleCat.{max u v} R)}
    (s : Cone G) (I : Ideal R)
    (h_ker : ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule R s.pt) ≤
        LinearMap.ker (PNatInverseSystem.Cone.stageMap s n).hom)
    [HasLimit G] :
    ModuleCat.of R (AdicCompletion I R ⊗[R] s.pt) ⟶ (limit G : ModuleCat R) :=
  ModuleCat.ofHom <|
    (PNatInverseSystem.Cone.adicCompletionComparison s I h_ker).hom ∘ₗ
      LinearMap.restrictScalars R (AdicCompletion.ofTensorProduct I s.pt)

/-- The tensor-to-limit comparison specialized to stagewise annihilation. -/
noncomputable def tensorToLimitOfAnnihilated
    {G : PNatInverseSystem (ModuleCat.{max u v} R)}
    (s : Cone G) (I : Ideal R)
    (h_annihilated : ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule R (G.stage n)) = ⊥)
    [HasLimit G] :
    ModuleCat.of R (AdicCompletion I R ⊗[R] s.pt) ⟶ (limit G : ModuleCat R) :=
  PNatInverseSystem.Cone.tensorToLimit s I
    (PNatInverseSystem.Cone.pow_smul_top_le_ker_stageMap_of_annihilated
      s I h_annihilated)

/-- Projecting the tensor-to-limit comparison to a stage evaluates the
completion tensor factor before applying the descended cone stage map. -/
theorem tensorToLimit_comp_limitProjection
    {G : PNatInverseSystem (ModuleCat.{max u v} R)}
    (s : Cone G) (I : Ideal R)
    (h_ker : ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule R s.pt) ≤
        LinearMap.ker (PNatInverseSystem.Cone.stageMap s n).hom)
    [HasLimit G] (n : ℕ+) :
    PNatInverseSystem.Cone.tensorToLimit s I h_ker ≫ G.limitProjection n =
      ModuleCat.ofHom
        ((PNatInverseSystem.Cone.adicQuotientStageMap s I h_ker n).comp
          ((AdicCompletion.eval I s.pt (n : ℕ)).comp
            (LinearMap.restrictScalars R (AdicCompletion.ofTensorProduct I s.pt)))) := sorry

end CategoryTheory.PNatInverseSystem.Cone

namespace CategoryTheory.PNatInverseSystem

variable {R : Type u} [CommRing R]

/-- The map from the `I ^ n` quotient of an inverse limit to its `n`th stage,
obtained by descending the canonical limit projection. -/
abbrev limitProjectionQuotient
    (F : PNatInverseSystem (ModuleCat.{v} R)) (I : Ideal R) [HasLimit F]
    (h_ker : ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule R (limit F : ModuleCat R)) ≤
        LinearMap.ker (F.limitProjectionLinearMap n))
    (n : ℕ+) :
    ((limit F : ModuleCat R) ⧸
        I ^ (n : ℕ) • (⊤ : Submodule R (limit F : ModuleCat R))) →ₗ[R] F.stage n :=
  (I ^ (n : ℕ) • (⊤ : Submodule R (limit F : ModuleCat R))).liftQ
    (F.limitProjectionLinearMap n) (h_ker n)

/-- The descended limit projection recovers the canonical projection on
quotient representatives. -/
theorem limitProjectionQuotient_comp_mkQ
    (F : PNatInverseSystem (ModuleCat.{v} R)) (I : Ideal R) [HasLimit F]
    (h_ker : ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule R (limit F : ModuleCat R)) ≤
        LinearMap.ker (F.limitProjectionLinearMap n))
    (n : ℕ+) :
    (F.limitProjectionQuotient I h_ker n).comp
        (Submodule.mkQ
          (I ^ (n : ℕ) • (⊤ : Submodule R (limit F : ModuleCat R)))) =
      F.limitProjectionLinearMap n := sorry

/-- If every positive stage is annihilated by the corresponding power of `I`,
then the same power is killed by the corresponding projection from the limit. -/
theorem pow_smul_top_le_ker_limitProjection_of_stagewise_annihilated
    (F : PNatInverseSystem (ModuleCat.{v} R)) (I : Ideal R) [HasLimit F]
    (h_annihilated : ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule R (F.stage n)) = ⊥) :
    ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule R (limit F : ModuleCat R)) ≤
        LinearMap.ker (F.limitProjectionLinearMap n) := sorry

/-- The canonical map from the adic completion of an inverse limit back to
that inverse limit, under a stagewise kernel condition. -/
noncomputable def completionToLimit
    (F : PNatInverseSystem (ModuleCat.{v} R)) (I : Ideal R) [HasLimit F]
    (h_ker : ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule R (limit F : ModuleCat R)) ≤
        LinearMap.ker (F.limitProjectionLinearMap n)) :
    ModuleCat.of R (AdicCompletion I (limit F : ModuleCat R)) ⟶ limit F :=
  CategoryTheory.PNatInverseSystem.Cone.adicCompletionComparison
    (limit.cone F) I h_ker

/-- The completion-to-limit map is a left inverse to the canonical map from
the limit into its adic completion. -/
theorem of_comp_completionToLimit
    (F : PNatInverseSystem (ModuleCat.{v} R)) (I : Ideal R) [HasLimit F]
    (h_ker : ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule R (limit F : ModuleCat R)) ≤
        LinearMap.ker (F.limitProjectionLinearMap n)) :
    ModuleCat.ofHom (AdicCompletion.of I (limit F : ModuleCat R)) ≫
        F.completionToLimit I h_ker = 𝟙 (limit F) := sorry

/-- Stagewise annihilation makes the inverse limit `I`-adically complete
whenever `I` is finitely generated. -/
@[stacks 0G1Q "adic completeness of an inverse limit"]
theorem isAdicComplete_limit_of_stagewise_annihilated
    (F : PNatInverseSystem (ModuleCat.{v} R)) (I : Ideal R) (h_finite : I.FG) [HasLimit F]
    (h_annihilated : ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule R (F.stage n)) = ⊥) :
    IsAdicComplete I (limit F : ModuleCat R) := sorry

/-- Successive kernel identifications imply the corresponding annihilation
condition at every positive stage. -/
theorem stagewise_annihilated_of_stepKernel
    (F : PNatInverseSystem (ModuleCat.{v} R)) (I : Ideal R)
    (h_step_surjective : ∀ n : ℕ+, Function.Surjective (F.stepLinearMap n))
    (h_step_kernel : ∀ n : ℕ+,
      LinearMap.ker (F.stepLinearMap n) =
        I ^ (n : ℕ) • (⊤ : Submodule R (F.stage (n + 1)))) :
    ∀ n : ℕ+, I ^ (n : ℕ) • (⊤ : Submodule R (F.stage n)) = ⊥ := sorry

/-- Under the successive quotient hypotheses, each descended projection from
the inverse limit is bijective. -/
theorem limitProjectionQuotient_bijective_of_successiveIdealPowerQuotients
    (F : PNatInverseSystem (ModuleCat.{v} R)) (I : Ideal R) (h_finite : I.FG) [HasLimit F]
    (h_step_surjective : ∀ n : ℕ+, Function.Surjective (F.stepLinearMap n))
    (h_step_kernel : ∀ n : ℕ+,
      LinearMap.ker (F.stepLinearMap n) =
        I ^ (n : ℕ) • (⊤ : Submodule R (F.stage (n + 1)))) :
    ∀ n : ℕ+,
      Function.Bijective
        (F.limitProjectionQuotient I
          (F.pow_smul_top_le_ker_limitProjection_of_stagewise_annihilated I
            (F.stagewise_annihilated_of_stepKernel I h_step_surjective h_step_kernel)) n) := sorry

/-- The canonical linear equivalence from the `I ^ n` quotient of the inverse
limit to stage `n` under the successive ideal-power quotient hypotheses. -/
@[stacks 09B8 "successive ideal-power quotient inverse limit"]
noncomputable def limitProjectionQuotientEquiv
    (F : PNatInverseSystem (ModuleCat.{v} R)) (I : Ideal R) (h_finite : I.FG) [HasLimit F]
    (h_step_surjective : ∀ n : ℕ+, Function.Surjective (F.stepLinearMap n))
    (h_step_kernel : ∀ n : ℕ+,
      LinearMap.ker (F.stepLinearMap n) =
        I ^ (n : ℕ) • (⊤ : Submodule R (F.stage (n + 1))))
    (n : ℕ+) :
    ((limit F : ModuleCat R) ⧸
        I ^ (n : ℕ) • (⊤ : Submodule R (limit F : ModuleCat R))) ≃ₗ[R] F.stage n :=
  LinearEquiv.ofBijective
    (F.limitProjectionQuotient I
      (F.pow_smul_top_le_ker_limitProjection_of_stagewise_annihilated I
        (F.stagewise_annihilated_of_stepKernel I h_step_surjective h_step_kernel)) n)
    (F.limitProjectionQuotient_bijective_of_successiveIdealPowerQuotients I h_finite
      h_step_surjective h_step_kernel n)

/-- The quotient equivalence for successive ideal-power quotients sends a
representative to its canonical inverse-limit projection. -/
theorem limitProjectionQuotientEquiv_apply_mk
    (F : PNatInverseSystem (ModuleCat.{v} R)) (I : Ideal R) (h_finite : I.FG) [HasLimit F]
    (h_step_surjective : ∀ n : ℕ+, Function.Surjective (F.stepLinearMap n))
    (h_step_kernel : ∀ n : ℕ+,
      LinearMap.ker (F.stepLinearMap n) =
        I ^ (n : ℕ) • (⊤ : Submodule R (F.stage (n + 1))))
    (n : ℕ+) (x : (limit F : ModuleCat R)) :
    F.limitProjectionQuotientEquiv I h_finite h_step_surjective h_step_kernel n
        (Submodule.Quotient.mk x) = F.limitProjectionLinearMap n x := sorry

/-- The inverse limit of successive ideal-power quotient stages is adically
complete. -/
@[stacks 09B8 "adic completeness after successive ideal-power quotients"]
theorem isAdicComplete_limit_of_successiveIdealPowerQuotients
    (F : PNatInverseSystem (ModuleCat.{v} R)) (I : Ideal R) (h_finite : I.FG) [HasLimit F]
    (h_step_surjective : ∀ n : ℕ+, Function.Surjective (F.stepLinearMap n))
    (h_step_kernel : ∀ n : ℕ+,
      LinearMap.ker (F.stepLinearMap n) =
        I ^ (n : ℕ) • (⊤ : Submodule R (F.stage (n + 1)))) :
    IsAdicComplete I (limit F : ModuleCat R) := sorry

end CategoryTheory.PNatInverseSystem
