module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Field.Basic
public import ReasLib.CategoryTheory.Monoidal.InvertiblePower
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_47_7_Irreducible
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal

/-!
# Lemma 72.14.4

An invertible module on a proper integral algebraic space over a field is trivial
when both it and its inverse have a nonzero global section.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.14.4: let `k` be a field and let `X` be a proper integral algebraic space
over `k` (decent, reduced, and with irreducible `|X|`). Let `L` be an invertible
`𝒪_X`-module. If `H⁰(X, L)` and `H⁰(X, L^{⊗-1})` are both nonzero, then `L ≅ 𝒪_X`. -/
@[stacks 0DMZ]
theorem isoUnit_of_nonzero_sections_inverse
    {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))}
    [Proper (toBase X)] [IsDecent X] [IsReduced X] [IsIrreducible X]
    (L : X.Modules) [isInvertibleObject L]
    (hL : ∃ s : L.sections, L.unitHomEquiv.symm s ≠ 0)
    (hLinv : ∃ t : (InvertiblePower.obj L (-1)).sections,
      (InvertiblePower.obj L (-1)).unitHomEquiv.symm t ≠ 0) :
    Nonempty (L ≅ (SheafOfModules.unit (structureSheaf X) : X.Modules)) :=
  sorry

/-- The morphism `𝒪_X ⟶ L` associated to a nonzero global section is an isomorphism
when `L` is invertible on a proper integral algebraic space over a field and the inverse
also has a nonzero global section. -/
theorem isIso_unitHom_of_nonzero_section_inverse
    {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))}
    [Proper (toBase X)] [IsDecent X] [IsReduced X] [IsIrreducible X]
    (L : X.Modules) [isInvertibleObject L]
    (s : L.sections) (hs : L.unitHomEquiv.symm s ≠ 0)
    (t : (InvertiblePower.obj L (-1)).sections)
    (ht : (InvertiblePower.obj L (-1)).unitHomEquiv.symm t ≠ 0) :
    IsIso (L.unitHomEquiv.symm s) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
