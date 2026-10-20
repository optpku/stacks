module

public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Trace

/-!
# Non-additivity of traces on distinguished triangles
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Pretriangulated DerivedCategory
open scoped CategoryTheory

namespace HomotopyCategory

/-- There is a distinguished triangle of perfect complexes over a ring with a triangle
endomorphism whose traces are not additive. -/
theorem exists_distinguishedTriangle_traceNatural_not_additive :
    ∃ (R : Type u) (_ : Ring R)
      (T : Triangle (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ))) (φ : T ⟶ T)
      (h₁ : IsPerfect (Qh.obj T.obj₁)) (h₂ : IsPerfect (Qh.obj T.obj₂))
      (h₃ : IsPerfect (Qh.obj T.obj₃)),
      T ∈ distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) ∧
        h₁.traceNatural (Qh.map φ.hom₁) + h₃.traceNatural (Qh.map φ.hom₃) ≠
          h₂.traceNatural (Qh.map φ.hom₂) := sorry

end HomotopyCategory
