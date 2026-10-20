/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.OpenImmersion

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

private theorem identity_rank_one (X : Scheme.{u}) :
    IsFiniteLocallyFreeOfRank (𝟙 X) 1 := by
  have hr : Scheme.Modules.IsFiniteLocallyFreeOfRank 1
      (Scheme.Hom.pushforwardStructureModule (𝟙 X)) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (M := SheafOfModules.unit X.ringCatSheaf)
      ((Scheme.Modules.pushforwardId X).app (SheafOfModules.unit X.ringCatSheaf)).symm
  exact
    { toIsFiniteLocallyFree :=
        { toIsAffineHom := inferInstance
          pushforward_isFiniteLocallyFree := hr.toIsFiniteLocallyFree }
      pushforward_isFiniteLocallyFreeOfRank := hr }

/-- Flat pullback along the identity, with its degree-zero grading identification,
is the identity on relative Chow groups. -/
theorem flatPullback_id
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (k : ℤ) :
    (AddEquiv.cast (M := fun n : ℤ ↦ RelativeChow δ X n) (add_zero k)).toAddMonoidHom.comp
      (@flatPullback S _ δ _ X X _ _ (𝟙 X) 0 inferInstance
        (by rw [Over.id_left]; infer_instance) k) =
      AddMonoidHom.id (RelativeChow δ X k) := by
  -- Local instance justification (proof-local temporary data): quotient descent uses local noetherianity induced by the given locally finite-type structure morphism.
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  -- Local instance justification (proof-local temporary data): cycle-level identity flat pullback requires relative dimension zero for the underlying over-category identity.
  letI : Scheme.Hom.RelativeDimension (𝟙 X : X ⟶ X).left 0 := by
    rw [Over.id_left]
    infer_instance
  -- Local instance justification (proof-local temporary data): the cycle push-pull formula requires the proved rank-one finite local freeness of the identity.
  letI : IsFiniteLocallyFreeOfRank (𝟙 X.left) 1 := identity_rank_one X.left
  have hc (α : CycleGroup X.left (X.hom.relativeDimensionFunction δ) k) :
      CycleGroup.reindex (X.hom.relativeDimensionFunction δ) (add_zero k)
        (CycleGroup.flatPullback δ X X (𝟙 X) 0 k α) = α := by
    simpa only [Over.id_left, CycleGroup.mapHom_id, AddMonoidHom.id_apply, one_nsmul] using
      CycleGroup.mapHom_flatPullback δ X X (𝟙 X) 1 k α
  apply AddMonoidHom.ext
  intro α
  obtain ⟨β, rfl⟩ := chowClass_surjective (X.hom.relativeDimensionFunction δ) k α
  change (AddEquiv.cast (M := fun n : ℤ ↦ RelativeChow δ X n) (add_zero k))
    (flatPullback δ X X (𝟙 X) 0 k (chowClass _ k β)) = chowClass _ k β
  rw [flatPullback_chowClass]
  have transport {a b : ℤ} (h : a = b)
      (γ : CycleGroup X.left (X.hom.relativeDimensionFunction δ) a) :
      (AddEquiv.cast (M := fun n : ℤ ↦ RelativeChow δ X n) h) (chowClass _ a γ) =
        chowClass _ b (CycleGroup.reindex (X.hom.relativeDimensionFunction δ) h γ) := by
    subst b
    rfl
  exact (transport (add_zero k) (CycleGroup.flatPullback δ X X (𝟙 X) 0 k β)).trans
    (congrArg (chowClass _ k) (hc β))

end AlgebraicGeometry.ChowGroup
