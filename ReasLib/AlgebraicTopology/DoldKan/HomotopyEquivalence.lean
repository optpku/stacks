module

public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import ReasLib.AlgebraicTopology.DoldKan.AlternatingFaceMapComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Short owner for the normalized--alternating homotopy equivalence

The Mathlib construction has a historical long name.  This leaf places the same canonical
equivalence under the Dold--Kan namespace, so downstream code can import a semantic owner without
depending on that implementation-level spelling.

@stack 0197
-/

@[expose] public section

open CategoryTheory
open AlgebraicTopology

noncomputable section

universe v u

namespace AlgebraicTopology.DoldKan

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The canonical homotopy equivalence from the normalized Moore complex to the alternating-face
complex of a simplicial object. -/
@[stacks 0197 "normalized Moore to alternating-face homotopy equivalence"]
noncomputable def mooreEquiv {Y : SimplicialObject A} :
    HomotopyEquiv ((normalizedMooreComplex A).obj Y)
      ((alternatingFaceMapComplex A).obj Y) :=
  homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex

end AlgebraicTopology.DoldKan
