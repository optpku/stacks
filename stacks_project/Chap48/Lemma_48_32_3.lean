/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.Triangle
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport

variable {S : Scheme.{u}} [IsNoetherian S]
variable {X Y : Scheme.FiniteTypeSeparatedOver S}

/- Lemma 48.32.3: a distinguished triangle of bounded coherent derived objects on `X`
admits a positive inverse system of distinguished triangles on `Y` whose three vertex systems
present the compactly supported pushforwards of the original vertices along `f`. -/
@[stacks 0G52] #check (AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.existsTriangle :
  ∀ (f : X ⟶ Y)
    (T : Pretriangulated.Triangle
      Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (hT : T ∈
      distTriang Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]),
    ∃ T_Y : PNatInverseSystem (Pretriangulated.Triangle
        Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]),
      (∀ n : ℕ+, T_Y.stage n ∈
        distTriang Dᵇ[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]) ∧
        IsPresentation f T.obj₁ (T_Y ⋙ Pretriangulated.Triangle.π₁) ∧
        IsPresentation f T.obj₂ (T_Y ⋙ Pretriangulated.Triangle.π₂) ∧
        IsPresentation f T.obj₃ (T_Y ⋙ Pretriangulated.Triangle.π₃))

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
