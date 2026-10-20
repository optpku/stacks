module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.HomologicalComplex.Flat
public import ReasLib.Algebra.Homology.HomologicalComplex.KFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-above termwise-flat complexes

@stack 06YQ

In an abelian monoidal category with exact countable coproducts, a bounded-above cochain complex
of flat objects is K-flat.  Exact countable coproducts are the natural hypothesis for the total
complex filtration; no filtered-colimit presentation is built into this API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace HomologicalComplex.IsTermwiseFlat

section


variable {C : Type u} [Category.{v} C] [Abelian C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [HasCountableCoproducts C] [CountableAB4 C]

/-- A bounded-above termwise-flat cochain complex is K-flat when countable coproducts are exact. -/
@[stacks 06YQ "categorical form"]
theorem isKFlat_of_boundedAbove {K : CochainComplex C ℤ}
    (hFlat : HomologicalComplex.IsTermwiseFlat K)
    (hbounded : CochainComplex.minus C K) :
    K.IsKFlat := sorry

end


end HomologicalComplex.IsTermwiseFlat
