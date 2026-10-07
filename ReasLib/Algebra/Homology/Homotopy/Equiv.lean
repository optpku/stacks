module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The morphism property of homotopy equivalences

This file equips Mathlib's shape-independent homotopy-equivalence morphism property with the
standard multiplicative and isomorphism-stability API. Functor-specific preservation theorems
can consequently be stated as inclusions into inverse images of this canonical property. It also
reexports the canonical `homotopic` relation for structured `HomRel.Equiv` images.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {ι : Type*} {c : ComplexShape ι}

namespace homotopyEquivalences

/-- Identity morphisms of homological complexes are homotopy equivalences. -/
@[stacks 019T "identity homotopy equivalence of complexes"]
theorem id (K : HomologicalComplex C c) :
    homotopyEquivalences C c (𝟙 K) := sorry

/-- A composite of homotopy equivalences of homological complexes is a homotopy equivalence. -/
@[stacks 019T "composition of homotopy equivalences of complexes"]
theorem comp {K L M : HomologicalComplex C c} {f : K ⟶ L} {g : L ⟶ M}
    (hf : homotopyEquivalences C c f) (hg : homotopyEquivalences C c g) :
    homotopyEquivalences C c (f ≫ g) := sorry

/-- Homotopy equivalences form a multiplicative morphism property on complexes of every shape. -/
@[stacks 019T "multiplicativity of homotopy equivalences of complexes"]
instance isMultiplicative : (homotopyEquivalences C c).IsMultiplicative := sorry

/-- Every isomorphism of homological complexes is a homotopy equivalence. -/
@[stacks 019T "isomorphisms are homotopy equivalences of complexes"]
theorem isomorphisms_le :
    CategoryTheory.MorphismProperty.isomorphisms (HomologicalComplex C c) ≤
      homotopyEquivalences C c := sorry

/-- Homotopy equivalences of homological complexes are stable under isomorphisms. -/
@[stacks 019T "isomorphism stability of homotopy equivalences of complexes"]
instance respectsIso : (homotopyEquivalences C c).RespectsIso := sorry

end homotopyEquivalences

end HomologicalComplex
