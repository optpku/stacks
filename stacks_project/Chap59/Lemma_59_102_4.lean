/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.EtaleComparison
import StacksCheckRecall

@[expose] public section

/-!
Lemma 59.102.4 (0F0I) is the concrete ph/étale comparison package on `Over S`.
The reusable owner is `AlgebraicGeometry.Scheme.PhComparison.situation`, with
coefficient family `torsionPiInverseImage` and morphism class `properOver`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PhComparison

universe u i

/- Lemma 59.102.4 (1): proper morphisms in `Over S` admit pullbacks. -/
@[stacks 0F0I]
#check (AlgebraicGeometry.Scheme.PhComparison.properOver_hasPullbacks :
    ∀ (S : Scheme.{u}),
    (properOver S).HasPullbacks)

/- Lemma 59.102.4 (1): proper morphisms in `Over S` are stable under base change. -/
@[stacks 0F0I]
#check (AlgebraicGeometry.Scheme.PhComparison.properOver_isStableUnderBaseChange :
    ∀ (S : Scheme.{u}),
    (properOver S).IsStableUnderBaseChange)

/- Lemma 59.102.4 (2): inverse image preserves the torsion `π⁻¹` coefficient family. -/
@[stacks 0F0I]
#check (AlgebraicGeometry.Scheme.PhComparison.torsionPiInverseImage_inverseImage_mem :
    ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    {ℱ : Sheaf ((S.overGrothendieckTopology @Etale).over Y) AddCommGrpCat.{u + 1}}
    (hℱ : torsionPiInverseImage Y ℱ),
    torsionPiInverseImage X
      (((S.overGrothendieckTopology @Etale).overMapPullback AddCommGrpCat.{u + 1} f).obj
        ℱ))

/- Lemma 59.102.4 (3): torsion `π⁻¹` coefficients are sheaves for the ph topology. -/
@[stacks 0F0I]
#check (AlgebraicGeometry.Scheme.PhComparison.torsionPiInverseImage_isSheafPh :
    ∀ {S : Scheme.{u}} {X : Over S}
    {ℱ : Sheaf ((S.overGrothendieckTopology @Etale).over X) AddCommGrpCat.{u + 1}}
    (hℱ : torsionPiInverseImage X ℱ),
    Presheaf.IsSheaf ((Scheme.bigPhSite S).over X) ℱ.1)

/- Lemma 59.102.4 (4): higher direct images along proper morphisms preserve `A'_X`. -/
@[stacks 0F0I]
#check (AlgebraicGeometry.Scheme.PhComparison.torsionPiInverseImage_higherDirectImage_mem :
    ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (hf : properOver S f) (n : ℕ)
    {ℱ : Sheaf ((S.overGrothendieckTopology @Etale).over X) AddCommGrpCat.{u + 1}}
    (hℱ : torsionPiInverseImage X ℱ),
    torsionPiInverseImage Y
      ((((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          ((S.overGrothendieckTopology @Etale).over X)
          ((S.overGrothendieckTopology @Etale).over Y)).rightDerived n).obj ℱ))

/- Lemma 59.102.4 (5): ph coverings admit étale refinements by proper morphisms. -/
@[stacks 0F0I]
#check (AlgebraicGeometry.Scheme.PhComparison.tau_covering_refinement :
    ∀ {S : Scheme.{u}} {U : Over S} {ι : Type i}
    (cover : ι → Over U)
    (hcover : ((Scheme.bigPhSite S).over U).CoversTop cover),
    ∃ (J : Type (max (u + 1) i)) (V : J → Over U),
      ((S.overGrothendieckTopology @Etale).over U).CoversTop V ∧
        ∃ (W : J → Over S) (f : ∀ idx, W idx ⟶ (V idx).left),
          ∀ idx,
            properOver S (f idx) ∧
              Sieve.generate (Presieve.singleton (f idx)) ∈
                  Scheme.bigPhSite S (V idx).left ∧
                ∃ (Kidx : Type (max (u + 1) i)) (Wcover : Kidx → Over (W idx)),
                  ((S.overGrothendieckTopology @Etale).over (W idx)).CoversTop
                      Wcover ∧
                    ∀ kj : Kidx,
                      ∃ i0 : ι,
                        Nonempty
                          ((Over.mk ((Wcover kj).hom ≫ f idx ≫ (V idx).hom)) ⟶
                            cover i0))

/- Lemma 59.102.4: the five source clauses are packaged by the concrete comparison situation. -/
@[stacks 0F0I]
#check (AlgebraicGeometry.Scheme.PhComparison.situation :
    ∀ (S : Scheme.{u}),
    TopologyComparison.Situation.{u + 1, u, i, max (u + 1) i, max (u + 1) i} (Scheme.bigPhSite S)
      (S.overGrothendieckTopology @Etale) (properOver S)
      (fun X ↦ torsionPiInverseImage X))

end
