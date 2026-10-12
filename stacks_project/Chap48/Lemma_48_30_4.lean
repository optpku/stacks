/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Triangle
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v

set_option synthInstance.maxHeartbeats 200000 in
/- Lemma 48.30.4: a distinguished triangle on an open subscheme extends to a positive inverse
system of distinguished triangles whose vertices are Deligne systems, and whose restriction is
the constant system on the original triangle. -/
@[stacks 0G4M] #check
  (@AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.exists_triangleSystem :
    ∀ {X U : Scheme.{v}} (j : U ⟶ X) [IsNoetherian X] [IsNoetherian U]
      [IsOpenImmersion j]
      (T : Pretriangulated.Triangle
        Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
      (hT : T ∈ Pretriangulated.distinguishedTriangles),
      ∃ (S₁ S₂ S₃ : AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem j)
        (Tₓ : PNatInverseSystem (Pretriangulated.Triangle
          Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])),
        (∀ n : ℕ+, Tₓ.stage n ∈
          distTriang Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) ∧
          Nonempty (Tₓ ⋙ Pretriangulated.Triangle.π₁ ⋙
              ambient (SheafOfModules.isCoherent X.ringCatSheaf) ≅ S₁.tower) ∧
          Nonempty (Tₓ ⋙ Pretriangulated.Triangle.π₂ ⋙
              ambient (SheafOfModules.isCoherent X.ringCatSheaf) ≅ S₂.tower) ∧
          Nonempty (Tₓ ⋙ Pretriangulated.Triangle.π₃ ⋙
              ambient (SheafOfModules.isCoherent X.ringCatSheaf) ≅ S₃.tower) ∧
          Nonempty (Tₓ ⋙ AlgebraicGeometry.Scheme.ModuleDerived.restrictionTriangle j ≅
            (Functor.const (OrderDual ℕ+)).obj
              ((ambient (SheafOfModules.isCoherent U.ringCatSheaf)).mapTriangle.obj T)))
