/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.CoproductRefinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Proetale.Family
public import ReasLib.RingTheory.Etale.WContractible
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# W-contractible schemes and finite coproduct refinements

Pro-étale finite coproduct Zariski refinements characterize
w-contractibility for affine schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.Proetale

/-- A scheme `T` has the finite coproduct Zariski refinement property if every
pro-étale cover of `T` admits a finite coproduct Zariski refinement. -/
def HasFiniteCoproductZariskiRefinement (T : Scheme.{u}) : Prop :=
  ∀ 𝒰 : T.Cover.{u} Scheme.proetalePrecoverage, 𝒰.HasFiniteCoproductZariskiRefinement

/-- A finite coproduct Zariski refinement property supplies a finite open
refinement and a coproduct isomorphism for each pro-étale cover. -/
theorem HasFiniteCoproductZariskiRefinement.exists_openCover {T : Scheme.{u}}
    (h : HasFiniteCoproductZariskiRefinement T)
    (𝒰 : T.Cover.{u} Scheme.proetalePrecoverage) :
    ∃ (𝒱 : T.OpenCover.{u}) (f : 𝒱.toPreZeroHypercover.Hom 𝒰.toPreZeroHypercover),
      Finite 𝒱.I₀ ∧ IsIso (Sigma.desc 𝒱.f) := sorry

/-- The finite coproduct Zariski refinement property is equivalent to its
indexed-family formulation for pro-étale covering families. -/
theorem hasFiniteCoproductZariskiRefinement_iff_family {T : Scheme.{u}} :
    HasFiniteCoproductZariskiRefinement T ↔
      ∀ {ι : Type v} (family : ι → Over T), IsCovering family →
        ∃ (𝒱 : T.OpenCover.{u}) (s : 𝒱.I₀ → ι)
          (h : (j : 𝒱.I₀) → 𝒱.X j ⟶ (family (s j)).left),
          Finite 𝒱.I₀ ∧ IsIso (Sigma.desc 𝒱.f) ∧
            ∀ j, h j ≫ (family (s j)).hom = 𝒱.f j := sorry

/-- The finite coproduct Zariski refinement property is equivalent to
pairwise disjointness of the open ranges in every pro-étale cover. -/
theorem hasFiniteCoproductZariskiRefinement_iff_pairwiseDisjoint {T : Scheme.{u}} :
    HasFiniteCoproductZariskiRefinement T ↔
      ∀ 𝒰 : T.Cover.{u} Scheme.proetalePrecoverage,
        ∃ (𝒱 : T.OpenCover.{u}) (f : 𝒱.toPreZeroHypercover.Hom 𝒰.toPreZeroHypercover),
          Finite 𝒱.I₀ ∧
            Pairwise fun i j ↦ Disjoint (𝒱.f i).opensRange (𝒱.f j).opensRange := sorry

end AlgebraicGeometry.Scheme.Proetale

namespace IsWContractibleRing

/-- A commutative ring `A` is w-contractible if and only if every pro-étale
cover of `Spec (.of A)` admits a finite coproduct Zariski refinement. -/
theorem iff_hasFiniteCoproductZariskiRefinement {A : Type u} [CommRing A] :
    IsWContractibleRing A ↔
      Scheme.Proetale.HasFiniteCoproductZariskiRefinement (Spec (.of A)) := sorry

/-- An affine scheme `T` has w-contractible global sections if and only if
every pro-étale cover of `T` admits a finite coproduct Zariski refinement. -/
theorem iff_hasFiniteCoproductZariskiRefinement_isAffine {T : Scheme.{u}} [IsAffine T] :
    IsWContractibleRing Γ(T, ⊤) ↔
      Scheme.Proetale.HasFiniteCoproductZariskiRefinement T := sorry

end IsWContractibleRing
