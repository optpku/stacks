/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_54_2_BivariantClass
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Theory

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace VirtualNormalBundle
namespace ShortExact

/-- Identifying the closed immersions with the underlying maps of `overHom` preserves
cartesian squares. -/
theorem isPullback_overHom_left
    {S Z X Z' X' : Scheme.{u}} (p : X ⟶ S) (p' : X' ⟶ S)
    (i : Z ⟶ X) (i' : Z' ⟶ X')
    (g : Over.mk (i' ≫ p') ⟶ Over.mk (i ≫ p))
    (f : Over.mk p' ⟶ Over.mk p)
    (square : IsPullback g.left i' i f.left) :
    IsPullback g.left (overHom (i' ≫ p') p' i' rfl).left
      (overHom (i ≫ p) p i rfl).left f.left := sorry

/-- The clopen locus on which a virtual-normal module has rank `r'` and an excess
quotient has rank `rE`. -/
noncomputable abbrev jointRankClopen {Z X : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i]
    (V' : VirtualNormalBundle i) (E : Z.Modules) [E.IsFiniteLocallyFree]
    (r' rE : ℕ) : Clopens Z :=
  @Scheme.Modules.rankClopen Z V'.module V'.isFiniteLocallyFree r' ⊓
    Scheme.Modules.rankClopen E rE

/-- `jointRankClopen` is the infimum of the two indicated rank clopens. -/
theorem jointRankClopen_def {Z X : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i]
    (V' : VirtualNormalBundle i) (E : Z.Modules) [E.IsFiniteLocallyFree]
    (r' rE : ℕ) :
    jointRankClopen V' E r' rE =
      @Scheme.Modules.rankClopen Z V'.module V'.isFiniteLocallyFree r' ⊓
        Scheme.Modules.rankClopen E rE := sorry

/-- Every open of the source of `overHom` lies in the preimage of the top open. -/
theorem overHom_preimage_top {S Z X : Scheme.{u}}
    (q : Z ⟶ S) (p : X ⟶ S) (i : Z ⟶ X) (hi : i ≫ p = q) (U : Z.Opens) :
    U ≤ (overHom q p i hi).left ⁻¹ᵁ (⊤ : X.Opens) := sorry

/-- The joint rank locus of a virtual-normal submodule and excess quotient lies in the
rank locus of the quotient. -/
theorem jointRankClopen_le_thirdRank {S Z X : Scheme.{u}}
    (p : X ⟶ S) (i : Z ⟶ X) [IsImmersion i]
    (V' : VirtualNormalBundle i) (E : Z.Modules) [E.IsFiniteLocallyFree]
    (r' rE : ℕ) :
    (jointRankClopen V' E r' rE).toOpens ≤
      (𝟙 (Over.mk (i ≫ p)) : Over.mk (i ≫ p) ⟶ Over.mk (i ≫ p)).left ⁻¹ᵁ
        (Scheme.Modules.rankClopen E rE).toOpens := sorry

/-- Lemma 42.54.4: in a cartesian square of closed immersions of schemes locally of finite
type over `S`, if `0 ⟶ V'.module ⟶ (pullback square V).module ⟶ E ⟶ 0` is a finite
locally free short exact sequence whose dual map factors the virtual-normal quotient, then
`res(c(Z ⟶ X, V)) = c_top(E) ∘ c(Z' ⟶ X', V')` on every joint rank locus. -/
@[stacks 0FV7]
theorem closedClassBaseChange_eq_topChern_comp
    {S Z X Z' X' : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (p' : X' ⟶ S) [LocallyOfFiniteType p']
    (i : Z ⟶ X) [LocallyOfFiniteType (i ≫ p)] [IsClosedImmersion i]
    (i' : Z' ⟶ X') [LocallyOfFiniteType (i' ≫ p')] [IsClosedImmersion i']
    (g : Over.mk (i' ≫ p') ⟶ Over.mk (i ≫ p)) (f : Over.mk p' ⟶ Over.mk p)
    (square : IsPullback g.left i' i f.left)
    (classes : ChernClass.Theory delta (i' ≫ p'))
    (V : VirtualNormalBundle i) (V' : VirtualNormalBundle i')
    (Vpull : VirtualNormalBundle i')
    (hVpull : Vpull = @pullback Z X Z' X' g.left i' i f.left
      (IsImmersion.instOfIsClosedImmersion i')
      (IsImmersion.instOfIsClosedImmersion i) square V)
    (D : ClosedSpecialization delta (i ≫ p) p i rfl V)
    (D' : ClosedSpecialization delta (i' ≫ p') p' i' rfl V') (E : Z'.Modules)
    (ι : V'.module ⟶ Vpull.module)
    (πE : Vpull.module ⟶ E) (hzero : ι ≫ πE = 0)
    [E.IsFiniteLocallyFree]
    (hshort : (ShortComplex.mk ι πE hzero).ShortExact)
    (hfactor : Vpull.map = Scheme.Modules.dualMap ι ≫ V'.map)
    (r' rE : ℕ) :
    DirectSum.of
      (fun n : ℕ ↦ BivariantClass delta
        (BivariantClass.OpenRestriction.hom (overHom (i' ≫ p') p' i' rfl)
          (jointRankClopen V' E r' rE).toOpens ⊤
          (overHom_preimage_top (i' ≫ p') p' i' rfl
            (jointRankClopen V' E r' rE).toOpens))
        (n : ℤ))
      (r' + rE)
      (BivariantClass.OpenRestriction.restrict delta
        (overHom (i' ≫ p') p' i' rfl) (r' + rE : ℤ)
        (jointRankClopen V' E r' rE).toOpens ⊤
        (overHom_preimage_top (i' ≫ p') p' i' rfl
          (jointRankClopen V' E r' rE).toOpens)
        (BivariantClass.restrict delta g (overHom (i' ≫ p') p' i' rfl) f
          (isPullback_overHom_left p p' i i' g f square) (r' + rE : ℤ)
          (globalClassOfRank delta (i ≫ p) p i rfl V D (r' + rE)))) =
      BivariantClass.Nonnegative.castHom delta
        (Category.id_comp
          (BivariantClass.OpenRestriction.hom (overHom (i' ≫ p') p' i' rfl)
            (jointRankClopen V' E r' rE).toOpens ⊤
            (overHom_preimage_top (i' ≫ p') p' i' rfl
              (jointRankClopen V' E r' rE).toOpens)))
        (BivariantClass.Nonnegative.comp delta
          (𝟙 (BivariantClass.OpenRestriction.over (Over.mk (i' ≫ p'))
            (jointRankClopen V' E r' rE).toOpens))
          (BivariantClass.OpenRestriction.hom (overHom (i' ≫ p') p' i' rfl)
            (jointRankClopen V' E r' rE).toOpens ⊤
            (overHom_preimage_top (i' ≫ p') p' i' rfl
              (jointRankClopen V' E r' rE).toOpens))
          (DirectSum.of
            (fun n : ℕ ↦ BivariantClass delta
              (𝟙 (BivariantClass.OpenRestriction.over (Over.mk (i' ≫ p'))
                (jointRankClopen V' E r' rE).toOpens))
              (n : ℤ)) rE
            (ChernClass.restrictComponent delta
              (BivariantClass.OpenRestriction.hom (𝟙 (Over.mk (i' ≫ p')))
                (jointRankClopen V' E r' rE).toOpens
                (Scheme.Modules.rankClopen E rE).toOpens
                (jointRankClopen_le_thirdRank p' i' V' E r' rE))
              rE
              (classes.baseComponent
                (BivariantClass.OpenRestriction.over (Over.mk (i' ≫ p'))
                  (Scheme.Modules.rankClopen E rE).toOpens)
                ((Scheme.Modules.pullback
                  (BivariantClass.OpenRestriction.ι (Over.mk (i' ≫ p'))
                    (Scheme.Modules.rankClopen E rE).toOpens).left).obj E)
                rE)))
          (DirectSum.of
            (fun n : ℕ ↦ BivariantClass delta
              (BivariantClass.OpenRestriction.hom (overHom (i' ≫ p') p' i' rfl)
                (jointRankClopen V' E r' rE).toOpens ⊤
                (overHom_preimage_top (i' ≫ p') p' i' rfl
                  (jointRankClopen V' E r' rE).toOpens))
              (n : ℤ)) r'
            (BivariantClass.OpenRestriction.restrict delta
              (overHom (i' ≫ p') p' i' rfl) (r' : ℤ)
              (jointRankClopen V' E r' rE).toOpens ⊤
              (overHom_preimage_top (i' ≫ p') p' i' rfl
                (jointRankClopen V' E r' rE).toOpens)
              (globalClassOfRank delta (i' ≫ p') p' i' rfl V' D' r')))) := sorry

end ShortExact
end VirtualNormalBundle
end Hom
end Scheme
end AlgebraicGeometry
