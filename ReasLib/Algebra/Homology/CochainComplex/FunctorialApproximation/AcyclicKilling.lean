module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.FunctorialApproximation

@[expose] public section

/-!
# Functorial approximations killing acyclic complexes

This module refines `FunctorialComplexApproximation` by recording that maps from a fixed family
of complexes become null-homotopic after the comparison map. The refinement itself makes sense
for an arbitrary family; acyclicity and the Grothendieck hypothesis occur only in its existence
theorem.
-/

open CategoryTheory

universe w v u

namespace CochainComplex

variable {I : Type w}

section Neutral

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryWithHomology C]

/-- A functorial acyclic-killing approximation is a functorial complex approximation such that
every map from a member of `K` becomes null-homotopic after the comparison map. -/
@[stacks 079M "functorial acyclic-killing approximation"]
structure FunctorialAcyclicKilling (K : I → CochainComplex C ℤ) extends
    toApproximation : FunctorialComplexApproximation C where
  /-- Every map from the selected family becomes null-homotopic after entering the
  approximation. -/
  nullHomotopic (i : I) (M : CochainComplex C ℤ) (f : K i ⟶ M) :
    Nonempty (Homotopy (f ≫ toApproximation.ι.app M) 0)

end Neutral

namespace FunctorialAcyclicKilling

section Grothendieck

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- Lemma 19.12.4: a family of acyclic complexes in a Grothendieck abelian category admits a
functorial acyclic-killing approximation. -/
@[stacks 079M "bundled existence"]
theorem nonempty (K : I → CochainComplex C ℤ) (hK : ∀ i, (K i).Acyclic) :
    Nonempty (FunctorialAcyclicKilling K) := sorry

/-- The unbundled existential view of a functorial acyclic-killing approximation. -/
@[stacks 079M "existential view"]
theorem exists_approximation (K : I → CochainComplex C ℤ) (hK : ∀ i, (K i).Acyclic) :
    ∃ J : FunctorialComplexApproximation C,
      ∀ (i : I) (M : CochainComplex C ℤ) (f : K i ⟶ M),
        Nonempty (Homotopy (f ≫ J.ι.app M) 0) := sorry

end Grothendieck

end FunctorialAcyclicKilling

end CochainComplex
