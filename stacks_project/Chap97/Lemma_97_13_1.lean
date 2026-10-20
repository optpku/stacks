/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FreeDimensionalAlgebra.ActionGroupoid
public import ReasLib.AlgebraicGeometry.Scheme.UniversalFiniteFree.Points
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

/- Lemma 97.13.1
The source conjugation C_g(m) = g⁻¹ m(g tensor g) is a right action for ordinary
matrix multiplication, realized here as a left action of the opposite group.
The historical source formula is ((g,m),(g',m')) ↦ (g*g',m').
The authorized local erratum corrects it to ((g,m),(g',m')) ↦ (g'*g,m')
in ordinary group coordinates, preserving conjugation and contravariant arrows. -/
@[stacks 05YP] #check (AlgebraicGeometry.FA.isoActionGroupoid :
  ∀ (d : ℕ) [NeZero d],
    AlgebraicGeometry.FA d ≅ AlgebraicGeometry.FA.actionGroupoid d)

#check (AlgebraicGeometry.FA.actionGroupoid :
  ∀ (d : ℕ) [NeZero d], Scheme.{0}ᵒᵖ ⥤ Grpd.{0, 0})
#check (UniversalFiniteFreeAlgebra.schemeHomEquiv :
  (T : Scheme.{0}) → (d : ℕ+) →
    (T ⟶ UniversalFiniteFreeAlgebra.baseScheme d) ≃ FreeDimAlgebra Γ(T, ⊤) d)
#check (AlgebraicGeometry.FA.pointArrowEquiv :
  ∀ (d : ℕ) [NeZero d] (T : Scheme.{0}),
    glFixOne Γ(T, ⊤) d ×
        (T ⟶ UniversalFiniteFreeAlgebra.baseScheme ⟨d, Nat.pos_of_neZero d⟩) ≃
      (Σ m : FreeDimAlgebra Γ(T, ⊤) d,
        Σ m' : FreeDimAlgebra Γ(T, ⊤) d, m ⟶ m'))
#check (AlgebraicGeometry.FA.arrowEquiv_source :
  ∀ {R : Type} [CommRing R] {d : ℕ} [NeZero d]
    (g : glFixOne R d) (m : FreeDimAlgebra R d),
    (AlgebraicGeometry.FA.arrowEquiv R d (g, m)).1 = m)
#check (AlgebraicGeometry.FA.homEquiv_comp :
  ∀ {R : Type} [CommRing R] {d : ℕ} [NeZero d]
    {m₁ m₂ m₃ : FreeDimAlgebra R d} (φ : m₁ ⟶ m₂) (ψ : m₂ ⟶ m₃),
    (AlgebraicGeometry.FA.homEquiv m₁ m₃ (φ ≫ ψ)).val =
      (AlgebraicGeometry.FA.homEquiv m₁ m₂ φ).val *
        (AlgebraicGeometry.FA.homEquiv m₂ m₃ ψ).val)
#check (AlgebraicGeometry.FA.arrowEquiv_target :
  ∀ {R : Type} [CommRing R] {d : ℕ} [NeZero d]
    (g : glFixOne R d) (m : FreeDimAlgebra R d),
    (AlgebraicGeometry.FA.arrowEquiv R d (g, m)).2.1 =
      FreeDimAlgebra.conjugate g m)
