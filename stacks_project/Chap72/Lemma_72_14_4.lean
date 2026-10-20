module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Invertible.Sections

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

/- Lemma 72.14.4: let `k` be a field and let `X` be a proper integral algebraic space
over `k`. Let `L` be an invertible
`𝒪_X`-module. If `H⁰(X, L)` and `H⁰(X, L^{⊗-1})` are both nonzero, then `L ≅ 𝒪_X`. -/
@[stacks 0DMZ] #check (AlgebraicGeometry.AlgebraicSpace.isoUnit_of_nonzero_sections_inverse :
    ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))}
    [Proper (SchemeRealization.toBase X)] [IsIntegral X]
    (L : X.Modules) [isInvertibleObject L]
    (hL : ∃ s : L.sections, L.unitHomEquiv.symm s ≠ 0)
    (hLinv : ∃ t : (InvertiblePower.obj L (-1)).sections,
      (InvertiblePower.obj L (-1)).unitHomEquiv.symm t ≠ 0),
    Nonempty (L ≅ (SheafOfModules.unit (structureSheaf X) : X.Modules)))

/- The morphism `𝒪_X ⟶ L` associated to a nonzero global section is an isomorphism
when `L` is invertible on a proper integral algebraic space over a field and the inverse
also has a nonzero global section. -/
#check (AlgebraicGeometry.AlgebraicSpace.isIso_unitHom_of_nonzero_section_inverse :
    ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))}
    [Proper (SchemeRealization.toBase X)] [IsIntegral X]
    (L : X.Modules) [isInvertibleObject L]
    (s : L.sections) (hs : L.unitHomEquiv.symm s ≠ 0)
    (t : (InvertiblePower.obj L (-1)).sections)
    (ht : (InvertiblePower.obj L (-1)).unitHomEquiv.symm t ≠ 0),
    IsIso (L.unitHomEquiv.symm s))

end AlgebraicGeometry.AlgebraicSpace
