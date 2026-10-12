/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.InverseSystem.Positive.Cone
public import ReasLib.RingTheory.AdicCompletion.QuotientSystem

/-!
# Limits of Positive Adic Quotient Systems

The positive quotient tower of a module has the adic completion as its limit.
This leaf packages that universal property and the comparison to the limit of
any positive module inverse system receiving a map from the quotient tower.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace AdicCompletion

variable {R : Type u} [CommRing R]

/-- Extend a cone on the positive adic quotient system by the trivial zeroth
quotient, obtaining the compatible family used by `AdicCompletion.lift`. -/
noncomputable def positiveQuotientConeFamily
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (s : Cone (positiveQuotientSystem I M)) (n : ℕ) :
    s.pt →ₗ[R] M ⧸ I ^ n • (⊤ : Submodule R M) :=
  if hn : 0 < n then
    (PNatInverseSystem.Cone.stageMap s ⟨n, hn⟩).hom
  else
    0

/-- The family obtained from a cone on the positive quotient tower is
compatible with all adic quotient transition maps. -/
theorem positiveQuotientConeFamily_compat
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (s : Cone (positiveQuotientSystem I M)) {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap I M hmn ∘ₗ
        positiveQuotientConeFamily I M s n =
      positiveQuotientConeFamily I M s m := sorry

/-- The evaluation maps from `AdicCompletion I M` form a cone over the
positive quotient system of `M`. -/
noncomputable def positiveQuotientEvaluationCone
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    Cone (positiveQuotientSystem I M) where
  pt := ModuleCat.of R (AdicCompletion I M)
  π :=
    { app := fun i ↦
        ModuleCat.ofHom (AdicCompletion.eval I M ((OrderDual.ofDual i : ℕ+) : ℕ))
      naturality := sorry }

/-- The evaluation cone of the adic completion is limiting for the positive
adic quotient system. -/
noncomputable def positiveQuotientEvaluationIsLimit
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    IsLimit (positiveQuotientEvaluationCone I M) where
  lift s :=
    ModuleCat.ofHom <|
      AdicCompletion.lift I
        (positiveQuotientConeFamily I M s)
        (positiveQuotientConeFamily_compat I M s)
  fac := sorry
  uniq := sorry

/-- The chosen limiting cone for the positive quotient system. -/
noncomputable def positiveQuotientLimitCone
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    LimitCone (positiveQuotientSystem I M) where
  cone := positiveQuotientEvaluationCone I M
  isLimit := positiveQuotientEvaluationIsLimit I M

/-- The inverse limit of the positive adic quotient system is canonically the
`I`-adic completion. -/
noncomputable def positiveQuotientLimitIso
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    limit (positiveQuotientSystem I M) ≅ ModuleCat.of R (AdicCompletion I M) :=
  limit.isoLimitCone (positiveQuotientLimitCone I M)

/-- The inverse of the quotient-system limit isomorphism has the expected
evaluation at every positive stage. -/
theorem positiveQuotientLimitIso_inv_comp_limitProjection
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ+) :
    (positiveQuotientLimitIso I M).inv ≫
        (positiveQuotientSystem I M).limitProjection n =
      ModuleCat.ofHom (AdicCompletion.eval I M (n : ℕ)) := sorry

/-- A morphism from the positive quotient system of `M` to `F` induces the
canonical map from `AdicCompletion I M` to `limit F`. -/
noncomputable def toLimit
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    {F : PNatInverseSystem (ModuleCat.{v} R)} [HasLimit F]
    (α : positiveQuotientSystem I M ⟶ F) :
    ModuleCat.of R (AdicCompletion I M) ⟶ limit F :=
  (positiveQuotientLimitIso I M).inv ≫ limMap α

/-- After identifying the quotient-system limit with the adic completion,
`toLimit` is exactly the induced map on limits. -/
theorem positiveQuotientLimitIso_hom_comp_toLimit
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    {F : PNatInverseSystem (ModuleCat.{v} R)} [HasLimit F]
    (α : positiveQuotientSystem I M ⟶ F) :
    (positiveQuotientLimitIso I M).hom ≫ toLimit I M α = limMap α := sorry

/-- Projecting `toLimit` to a positive stage is evaluation at that quotient
followed by the corresponding component of the quotient-system morphism. -/
theorem toLimit_comp_limitProjection
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    {F : PNatInverseSystem (ModuleCat.{v} R)} [HasLimit F]
    (α : positiveQuotientSystem I M ⟶ F) (n : ℕ+) :
    toLimit I M α ≫ F.limitProjection n =
      ModuleCat.ofHom (AdicCompletion.eval I M (n : ℕ)) ≫
        PNatInverseSystem.NatTrans.stageMap α n := sorry

end AdicCompletion
