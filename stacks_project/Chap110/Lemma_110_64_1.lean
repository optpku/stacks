module

public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Basic
public import stacks_project.Chap64.Proposition_64_10_2_Trace

/-!
# Non-additivity of traces on distinguished triangles
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Pretriangulated DerivedCategory
open scoped CategoryTheory

namespace CategoryTheory.HomotopyCategory

/-- Lemma 110.64.1: there exists a ring `R`, a distinguished triangle `T` in
the homotopy category `K(ModuleCat R)`, and an endomorphism `φ : T ⟶ T`, such
that the vertices of `T` are perfect complexes and
`h₁.traceNatural (Qh.map φ.hom₁) + h₃.traceNatural (Qh.map φ.hom₃)` is not equal
to `h₂.traceNatural (Qh.map φ.hom₂)`. -/
@[stacks 087L]
theorem exists_perfect_distinguishedTriangle_endomorphism_traceNatural_not_additive :
    ∃ (R : Type u) (_ : Ring R) (T : Triangle (K((ModuleCat.{u} R)))) (φ : T ⟶ T)
      (h₁ : IsPerfect (Qh.obj T.obj₁)) (h₂ : IsPerfect (Qh.obj T.obj₂))
      (h₃ : IsPerfect (Qh.obj T.obj₃)),
      T ∈ distTriang (K((ModuleCat.{u} R))) ∧
        h₁.traceNatural (Qh.map φ.hom₁) + h₃.traceNatural (Qh.map φ.hom₃) ≠
          h₂.traceNatural (Qh.map φ.hom₂) :=
  sorry

/-- Traces of endomorphisms of perfect complexes need not be additive on
endomorphisms of distinguished triangles in the homotopy category `K(R)`. -/
theorem not_traceNatural_additive_on_distinguishedTriangle_endomorphism :
    ¬ ∀ (R : Type u) [Ring R] (T : Triangle (K((ModuleCat.{u} R)))) (φ : T ⟶ T)
        (h₁ : IsPerfect (Qh.obj T.obj₁)) (h₂ : IsPerfect (Qh.obj T.obj₂))
        (h₃ : IsPerfect (Qh.obj T.obj₃)),
        T ∈ distTriang (K((ModuleCat.{u} R))) →
          h₁.traceNatural (Qh.map φ.hom₁) + h₃.traceNatural (Qh.map φ.hom₃) =
            h₂.traceNatural (Qh.map φ.hom₂) :=
  sorry

end CategoryTheory.HomotopyCategory
