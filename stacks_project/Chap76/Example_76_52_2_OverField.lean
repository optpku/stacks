module

public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap75.Lemma_75_13_7_PseudoCoherent
public import stacks_project.Chap76.Lemma_76_52_4_Relative

/-!
# Relative perfectness over a field

This file characterizes `k`-perfect derived modules on algebraic spaces of finite
presentation over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open DerivedCategory.TStructure

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The unique morphism from an algebraic space over the spectrum of a field to
that spectrum is flat. -/
instance instFlat_toBase {k : Type u} [Field k] (X : AlgebraicSpace (Spec (.of k))) :
    Flat (toBase X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.OverField

/-- A derived module on an algebraic space of finite presentation over a field is
perfect relative to the field if and only if it is cohomologically bounded and
pseudo-coherent. Finite presentation of the structure morphism includes
quasi-compactness of the source. -/
theorem isPerfectRelativeTo_iff_bounded_and_pseudoCoherent {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (.of k))) [FinitePresentation (toBase X)]
    (E : ModuleDerived X) :
    IsPerfectRelativeTo (toBase X) E ↔
      (t.bounded : ObjectProperty (ModuleDerived X)) E ∧ IsPseudoCoherent X E :=
  sorry

/-- A derived module on an algebraic space of finite presentation over a field is
perfect relative to the field if and only if it is cohomologically bounded and has
coherent cohomology in every degree, equivalently if it lies in
`t.bounded ⊓ cohomologyIn (SheafOfModules.isCoherent (structureSheaf X))`. This is a
relative condition and does not assert perfectness on every fibre. -/
theorem isPerfectRelativeTo_iff_bounded_and_coherentCohomology {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (.of k))) [FinitePresentation (toBase X)]
    (E : ModuleDerived X) :
    IsPerfectRelativeTo (toBase X) E ↔
      (t.bounded : ObjectProperty (ModuleDerived X)) E ∧
        DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent (structureSheaf X)) E :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.OverField
