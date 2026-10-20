/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.EtaleCohomology
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Situation

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u i

namespace AlgebraicGeometry.Scheme.HComparison

/-- The isomorphism-closed family of sheaves on `(Sch/X)_étale` isomorphic to
`π_X⁻¹ F` for a locally torsion abelian sheaf `F` on `X_étale`. -/
abbrev torsionPullback (X : Scheme.{u}) :
    ObjectProperty (Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1}) :=
  (Sheaf.torsion X.smallEtaleTopology).map (FppfEtale.piInverseImage X)

/-- Small-to-big inverse images of locally torsion abelian sheaves form a weak Serre class. -/
instance torsionPullback_isWeakSerre (X : Scheme.{u}) :
    IsWeakSerreClass (torsionPullback X) := sorry

/-- Every étale covering of schemes is an h covering. -/
theorem etale_le_h : etaleTopology.{u} ≤ hPrecoverage.toGrothendieck := sorry

/-- Abelian sheaves on big étale slices have injective resolutions at the
topology-comparison coefficient universe. -/
instance etaleOver_hasInjectiveResolutions (X : Scheme.{u}) :
    HasInjectiveResolutions
      (Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1}) := sorry

/-- Inverse image along a morphism of schemes preserves the torsion-pullback
coefficient family. -/
theorem inverseImage_mem {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : Sheaf (etaleTopology.over Y) AddCommGrpCat.{u + 1}}
    (hF : torsionPullback Y F) :
    torsionPullback X ((etaleTopology.overMapPullback AddCommGrpCat.{u + 1} f).obj F) :=
  sorry

/-- A torsion-pullback coefficient sheaf on `(Sch/X)_étale` is a sheaf for the
h topology on schemes over `X`. -/
theorem isSheafH {X : Scheme.{u}}
    {F : Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1}}
    (hF : torsionPullback X F) :
    Presheaf.IsSheaf (hPrecoverage.toGrothendieck.over X) F.1 := sorry

/-- Higher direct images of torsion-pullback coefficients along a proper morphism
remain in the torsion-pullback family. -/
theorem higherDirectImage_mem {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsProper f)
    (i : ℕ) {F : Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1}}
    (hF : torsionPullback X F) :
    torsionPullback Y
      ((((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (etaleTopology.over X) (etaleTopology.over Y)).rightDerived i).obj F) :=
  sorry

/-- An h covering of `U` admits an étale covering refinement whose members factor
through proper singleton h coverings followed by étale coverings. -/
theorem covering_refinement {U : Scheme.{u}} {ι : Type i} (cover : ι → Over U)
    (hcover : (hPrecoverage.toGrothendieck.over U).CoversTop cover) :
    ∃ (J : Type (max (u + 1) i)) (V : J → Over U),
      (etaleTopology.over U).CoversTop V ∧
        ∃ (W : J → Scheme.{u}) (f : ∀ j, W j ⟶ (V j).left),
          ∀ j, IsProper (f j) ∧
            Sieve.generate (Presieve.singleton (f j)) ∈
                hPrecoverage.toGrothendieck (V j).left ∧
              ∃ (Kj : Type (max (u + 1) i)) (Wcoverj : Kj → Over (W j)),
                (etaleTopology.over (W j)).CoversTop Wcoverj ∧
                  ∀ k : Kj, ∃ i : ι,
                    Nonempty
                      (Over.mk ((Wcoverj k).hom ≫ f j ≫ (V j).hom) ⟶ cover i) :=
  sorry

/-- Proper morphisms and locally torsion small-to-big étale coefficients satisfy the
closure and covering-refinement conditions for h/étale cohomology comparison. -/
instance comparisonSituation :
    TopologyComparison.Situation.{u + 1, u, i, max (u + 1) i, max (u + 1) i}
      hPrecoverage.toGrothendieck etaleTopology (@IsProper)
      (fun X ↦ torsionPullback X) where
  isWeakSerre X := torsionPullback_isWeakSerre X
  hasPullbacks := inferInstance
  isStableUnderBaseChange := inferInstance
  inverseImage_mem := inverseImage_mem
  isSheaf_for_finer_topology := isSheafH
  higherDirectImage_mem := by
    intro _ _ _ X Y f hf n F hF
    exact higherDirectImage_mem f hf n hF
  tau_covering_refinement := covering_refinement

end AlgebraicGeometry.Scheme.HComparison

end

end
