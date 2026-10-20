module

public import Mathlib.Algebra.Field.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.CategoryTheory.Monoidal.InvertiblePower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Sections of invertible modules on proper integral algebraic spaces

An invertible module on a proper integral algebraic space over a field is trivial
when both it and its inverse have a nonzero global section.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An invertible module on a proper integral algebraic space over a field is isomorphic
to the structure module if both it and its tensor inverse have nonzero global sections. -/
theorem isoUnit_of_nonzero_sections_inverse
    {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))}
    [Proper (SchemeRealization.toBase X)] [IsIntegral X]
    (L : X.Modules) [isInvertibleObject L]
    (hL : ∃ s : L.sections, L.unitHomEquiv.symm s ≠ 0)
    (hLinv : ∃ t : (InvertiblePower.obj L (-1)).sections,
      (InvertiblePower.obj L (-1)).unitHomEquiv.symm t ≠ 0) :
    Nonempty (L ≅ (SheafOfModules.unit (structureSheaf X) : X.Modules)) :=
  sorry

/-- The morphism from the structure module associated to a nonzero global section of an
invertible module on a proper integral algebraic space over a field is an isomorphism
if the tensor inverse also has a nonzero global section. -/
theorem isIso_unitHom_of_nonzero_section_inverse
    {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))}
    [Proper (SchemeRealization.toBase X)] [IsIntegral X]
    (L : X.Modules) [isInvertibleObject L]
    (s : L.sections) (hs : L.unitHomEquiv.symm s ≠ 0)
    (t : (InvertiblePower.obj L (-1)).sections)
    (ht : (InvertiblePower.obj L (-1)).unitHomEquiv.symm t ≠ 0) :
    IsIso (L.unitHomEquiv.symm s) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
