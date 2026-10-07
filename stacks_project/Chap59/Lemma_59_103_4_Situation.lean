module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Presentation
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Situation
public import stacks_project.Chap59.Lemma_59_103_4_TorsionPullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HComparison

/-- Every étale covering of schemes is an h covering. -/
theorem etale_le_h : etaleTopology.{u} ≤ hPrecoverage.toGrothendieck := sorry

/-- Abelian sheaves on big étale slices have injective resolutions at the
topology-comparison coefficient universe. -/
instance etaleOver_hasInjectiveResolutions (X : Scheme.{u}) :
    HasInjectiveResolutions
      (Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1}) := sorry

/-- Direct image of abelian sheaves along postcomposition on big étale slices is
additive. -/
instance overMap_sheafPushforwardCocontinuous_additive
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (etaleTopology.over X) (etaleTopology.over Y)).Additive := sorry

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
through proper morphisms that are h coverings, as in Situation 21.30.1 (5). -/
theorem covering_refinement {U : Scheme.{u}} {ι : Type u} (cover : ι → Over U)
    (hcover : (hPrecoverage.toGrothendieck.over U).CoversTop cover) :
    ∃ (J : Type u) (V : J → Over U),
      (etaleTopology.over U).CoversTop V ∧
        ∃ (W : J → Scheme.{u}) (f : ∀ j, W j ⟶ (V j).left),
          ∀ j, IsProper (f j) ∧
            Sieve.generate (Presieve.singleton (f j)) ∈
                hPrecoverage.toGrothendieck (V j).left ∧
              ∃ (Kj : Type u) (Wcoverj : Kj → Over (W j)),
                (etaleTopology.over (W j)).CoversTop Wcoverj ∧
                  ∀ k : Kj, ∃ i : ι,
                    Nonempty
                      (Over.mk ((Wcoverj k).hom ≫ f j ≫ (V j).hom) ⟶ cover i) :=
  sorry

/-- The h/étale comparison on schemes, with proper morphisms and the
torsion-pullback coefficient family, satisfies Situation 21.30.1. -/
instance comparisonSituation :
    TopologyComparison.Situation.{u + 1, u, u, u, u}
      hPrecoverage.toGrothendieck etaleTopology (@IsProper)
      (fun X ↦ torsionPullback X) := sorry

end AlgebraicGeometry.Scheme.HComparison

end

end
