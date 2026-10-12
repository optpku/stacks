/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap42.Lemma_42_44_2
public import stacks_project.Chap42.Lemma_42_54_2_BivariantClass

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.ShortExact
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace VirtualNormalBundle
namespace ShortExact

/-- A joint rank locus for a short exact sequence maps into the top open of the
ambient target. -/
theorem rankPairClopen_le_preimage_top
    {S Z X : Scheme.{u}} (p : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]
    (V' V : VirtualNormalBundle i) (E : Z.Modules)
    (ι : V'.module ⟶ V.module) (πE : V.module ⟶ E) (hzero : ι ≫ πE = 0)
    [E.IsFiniteLocallyFree] (r' rE : ℕ) :
    (@rankPairClopen
      Z (CategoryTheory.ShortComplex.mk ι πE hzero) V'.isFiniteLocallyFree
      (inferInstance : E.IsFiniteLocallyFree) r' rE).toOpens ≤
      (overHom (i ≫ p) p i rfl).left ⁻¹ᵁ (⊤ : X.Opens) := sorry

/-- The restriction of the closed immersion to the joint rank locus of the subbundle
and quotient. -/
noncomputable def rankPairHom
    {S Z X : Scheme.{u}} (p : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]
    (V' V : VirtualNormalBundle i) (E : Z.Modules)
    (ι : V'.module ⟶ V.module) (πE : V.module ⟶ E) (hzero : ι ≫ πE = 0)
    [E.IsFiniteLocallyFree] (r' rE : ℕ) :
    @rankPairOver
        S (Over.mk (i ≫ p)) (CategoryTheory.ShortComplex.mk ι πE hzero)
        V'.isFiniteLocallyFree (inferInstance : E.IsFiniteLocallyFree) r' rE ⟶
      BivariantClass.OpenRestriction.over (Over.mk p) ⊤ :=
  BivariantClass.OpenRestriction.hom
    (overHom (i ≫ p) p i rfl)
    (@rankPairClopen
      Z (CategoryTheory.ShortComplex.mk ι πE hzero) V'.isFiniteLocallyFree
      (inferInstance : E.IsFiniteLocallyFree) r' rE).toOpens ⊤
    (rankPairClopen_le_preimage_top p i V' V E ι πE hzero r' rE)

/-- `rankPairHom` is the canonical open restriction of the original closed immersion. -/
theorem rankPairHom_def
    {S Z X : Scheme.{u}} (p : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]
    (V' V : VirtualNormalBundle i) (E : Z.Modules)
    (ι : V'.module ⟶ V.module) (πE : V.module ⟶ E) (hzero : ι ≫ πE = 0)
    [E.IsFiniteLocallyFree] (r' rE : ℕ) :
    rankPairHom p i V' V E ι πE hzero r' rE =
      BivariantClass.OpenRestriction.hom
        (overHom (i ≫ p) p i rfl)
        (@rankPairClopen
          Z (CategoryTheory.ShortComplex.mk ι πE hzero) V'.isFiniteLocallyFree
          (inferInstance : E.IsFiniteLocallyFree) r' rE).toOpens ⊤
        (rankPairClopen_le_preimage_top p i V' V E ι πE hzero r' rE) := sorry

/-- The homogeneous virtual-normal class restricted to a common joint rank locus. -/
noncomputable def restrictedGlobalClass
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [IsClosedImmersion i] (V' V W : VirtualNormalBundle i)
    (E : Z.Modules) (ι : V'.module ⟶ V.module) (πE : V.module ⟶ E)
    (hzero : ι ≫ πE = 0) [E.IsFiniteLocallyFree]
    (D : ClosedSpecialization delta (i ≫ p) p i rfl W) (r' rE n : ℕ) :
    BivariantClass delta (rankPairHom p i V' V E ι πE hzero r' rE) (n : ℤ) :=
  BivariantClass.OpenRestriction.restrict delta
    (overHom (i ≫ p) p i rfl) (n : ℤ)
    (@rankPairClopen
      Z (CategoryTheory.ShortComplex.mk ι πE hzero) V'.isFiniteLocallyFree
      (inferInstance : E.IsFiniteLocallyFree) r' rE).toOpens ⊤
    (rankPairClopen_le_preimage_top p i V' V E ι πE hzero r' rE)
    (globalClassOfRank delta (i ≫ p) p i rfl W D n)

/-- `restrictedGlobalClass` is open restriction of the global homogeneous
virtual-normal class. -/
theorem restrictedGlobalClass_def
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [IsClosedImmersion i] (V' V W : VirtualNormalBundle i)
    (E : Z.Modules) (ι : V'.module ⟶ V.module) (πE : V.module ⟶ E)
    (hzero : ι ≫ πE = 0) [E.IsFiniteLocallyFree]
    (D : ClosedSpecialization delta (i ≫ p) p i rfl W) (r' rE n : ℕ) :
    restrictedGlobalClass delta p i V' V W E ι πE hzero D r' rE n =
      BivariantClass.OpenRestriction.restrict delta
        (overHom (i ≫ p) p i rfl) (n : ℤ)
        (@rankPairClopen
          Z (CategoryTheory.ShortComplex.mk ι πE hzero) V'.isFiniteLocallyFree
          (inferInstance : E.IsFiniteLocallyFree) r' rE).toOpens ⊤
        (rankPairClopen_le_preimage_top p i V' V E ι πE hzero r' rE)
        (globalClassOfRank delta (i ≫ p) p i rfl W D n) := sorry

/-- Composing the identity of the joint rank locus with `rankPairHom` leaves the
morphism unchanged. -/
theorem id_comp_rankPairHom
    {S Z X : Scheme.{u}} (p : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]
    (V' V : VirtualNormalBundle i) (E : Z.Modules)
    (ι : V'.module ⟶ V.module) (πE : V.module ⟶ E) (hzero : ι ≫ πE = 0)
    [E.IsFiniteLocallyFree] (r' rE : ℕ) :
    𝟙 (@rankPairOver
        S (Over.mk (i ≫ p)) (CategoryTheory.ShortComplex.mk ι πE hzero)
        V'.isFiniteLocallyFree (inferInstance : E.IsFiniteLocallyFree) r' rE) ≫
      rankPairHom p i V' V E ι πE hzero r' rE =
        rankPairHom p i V' V E ι πE hzero r' rE := sorry

/-- Lemma 42.54.3: for a short exact sequence `0 ⟶ V'.module ⟶ V.module ⟶ E ⟶ 0`
whose dual inclusion factors the virtual-normal quotient map, the virtual-normal class
of `V` is the composition of the top Chern class of `E` with that of `V'`, on every
joint rank locus. -/
@[stacks 0FBL]
theorem closedClass_eq_topChern_comp
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [IsClosedImmersion i] (classes : ChernClass.Theory delta (i ≫ p))
    (V' V : VirtualNormalBundle i) (E : Z.Modules)
    (ι : V'.module ⟶ V.module) (πE : V.module ⟶ E) (hzero : ι ≫ πE = 0)
    [E.IsFiniteLocallyFree]
    (hshort : (CategoryTheory.ShortComplex.mk ι πE hzero).ShortExact)
    (hfactor : V.map = Scheme.Modules.dualMap ι ≫ V'.map)
    (D' : ClosedSpecialization delta (i ≫ p) p i rfl V')
    (D : ClosedSpecialization delta (i ≫ p) p i rfl V) (r' rE : ℕ) :
    DirectSum.of
        (fun n : ℕ ↦ BivariantClass delta
          (rankPairHom p i V' V E ι πE hzero r' rE) (n : ℤ))
        (r' + rE)
        (restrictedGlobalClass delta p i V' V V E ι πE hzero D r' rE (r' + rE)) =
      BivariantClass.Nonnegative.castHom delta
        (id_comp_rankPairHom p i V' V E ι πE hzero r' rE)
        (BivariantClass.Nonnegative.comp delta
          (𝟙 (@rankPairOver
            S (Over.mk (i ≫ p)) (CategoryTheory.ShortComplex.mk ι πE hzero)
            V'.isFiniteLocallyFree (inferInstance : E.IsFiniteLocallyFree) r' rE))
          (rankPairHom p i V' V E ι πE hzero r' rE)
          (DirectSum.of
            (fun n : ℕ ↦ BivariantClass delta
              (𝟙 (@rankPairOver
                S (Over.mk (i ≫ p)) (CategoryTheory.ShortComplex.mk ι πE hzero)
                V'.isFiniteLocallyFree (inferInstance : E.IsFiniteLocallyFree) r' rE))
              (n : ℤ)) rE
            (@rankPairTopChern
              S _ delta _ (Over.mk (i ≫ p)) _ classes
              (CategoryTheory.ShortComplex.mk ι πE hzero) V'.isFiniteLocallyFree
              (inferInstance : E.IsFiniteLocallyFree) r' rE))
          (DirectSum.of
            (fun n : ℕ ↦ BivariantClass delta
              (rankPairHom p i V' V E ι πE hzero r' rE) (n : ℤ)) r'
            (restrictedGlobalClass delta p i V' V V' E ι πE hzero D' r' rE r'))) := sorry

end ShortExact
end VirtualNormalBundle
end Hom
end Scheme
end AlgebraicGeometry
