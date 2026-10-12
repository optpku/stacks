/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph
public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Refinements by standard ph coverings

Standard ph coverings refine Zariski open covers of affine schemes and
dependent composites of standard ph coverings.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.StandardPhCovering

/-- Every Zariski open cover of an affine scheme admits a standard ph covering
whose charts factor through members of the original cover. -/
theorem exists_refinement_of_openCover {T : Scheme.{u}} [IsAffine T]
    (𝒰 : T.OpenCover.{v}) :
    ∃ Φ : StandardPhCovering T,
      ∀ j : Fin Φ.m, ∃ i : 𝒰.I₀, ∃ g : Φ.obj j ⟶ 𝒰.X i,
        g ≫ 𝒰.f i = Φ.map j := sorry

/-- A dependent composite of standard ph coverings of an affine scheme admits
a standard ph refinement whose charts factor through the composite family. -/
theorem exists_refinement_of_comp {T : Scheme.{u}} [IsAffine T]
    (Φ : StandardPhCovering T)
    (Ψ : ∀ j : Fin Φ.m, StandardPhCovering (Φ.obj j)) :
    ∃ Ω : StandardPhCovering T,
      ∀ k : Fin Ω.m,
        ∃ p : Sigma fun j : Fin Φ.m ↦ Fin (Ψ j).m,
          ∃ g : Ω.obj k ⟶ (Ψ p.1).obj p.2,
            g ≫ (Ψ p.1).map p.2 ≫ Φ.map p.1 = Ω.map k := sorry

end AlgebraicGeometry.StandardPhCovering

namespace AlgebraicGeometry.Scheme.OpenCover

/-- The family of morphisms underlying a Zariski open cover is a ph covering. -/
instance phCovering {T : Scheme.{u}} (cover : T.OpenCover.{v}) :
    PhCovering (fun i : cover.I₀ ↦ cover.X i) (fun i ↦ cover.f i) := sorry

end AlgebraicGeometry.Scheme.OpenCover
