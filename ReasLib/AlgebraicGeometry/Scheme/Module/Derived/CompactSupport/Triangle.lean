/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Triangle

/-!
# Distinguished triangles presenting compactly supported pushforwards

This module constructs positive inverse systems of distinguished triangles whose vertices
present the compactly supported pushforwards of a given distinguished triangle.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport

variable {S : Scheme.{u}} [IsNoetherian S]
variable {X Y : Scheme.FiniteTypeSeparatedOver S}

/-- A distinguished triangle of bounded coherent derived objects admits a positive inverse
system of distinguished triangles whose vertex systems present its compactly supported
pushforwards. -/
theorem existsTriangle (f : X ⟶ Y)
    (T : Pretriangulated.Triangle
      Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (hT : T ∈ Pretriangulated.distinguishedTriangles) :
    ∃ T_Y : PNatInverseSystem (Pretriangulated.Triangle
        Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]),
      (∀ n : ℕ+, T_Y.stage n ∈
        distTriang Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]) ∧
        IsPresentation f T.obj₁ (T_Y ⋙ Pretriangulated.Triangle.π₁) ∧
        IsPresentation f T.obj₂ (T_Y ⋙ Pretriangulated.Triangle.π₂) ∧
        IsPresentation f T.obj₃ (T_Y ⋙ Pretriangulated.Triangle.π₃) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
