module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Views.Rows
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Category.IsIso

/-!
# Isomorphism views of Cartan--Eilenberg maps

An isomorphism of resolving double complexes induces isomorphisms on every standard column,
row, bidegree, cycles, image, and homology view.  These instances keep the view API compositional
for comparison and change-of-resolution arguments.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex₂

noncomputable section

universe v u

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}

/-- A double-complex isomorphism induces an isomorphism on every column. -/
@[stacks 015J "isomorphism on Cartan-Eilenberg columns"]
instance column_isIso (f : Map I J) (p : ℤ) [IsIso f.hom] : IsIso (column f p) := sorry

/-- A double-complex isomorphism induces an isomorphism on every row. -/
@[stacks 015J "isomorphism on Cartan-Eilenberg rows"]
instance row_isIso (f : Map I J) (q : ℤ) [IsIso f.hom] : IsIso (row f q) := sorry

/-- A double-complex isomorphism induces an isomorphism in every bidegree. -/
@[stacks 015J "isomorphism on Cartan-Eilenberg bidegrees"]
instance term_isIso (f : Map I J) (p q : ℤ) [IsIso f.hom] : IsIso (term f p q) := sorry

/-- A column isomorphism induces an isomorphism on horizontal cycles. -/
@[stacks 015J "isomorphism on Cartan-Eilenberg column cycles"]
instance cyclesColumn_isIso (f : Map I J) (p : ℤ) [IsIso f.hom] :
    IsIso (cyclesColumn f p) := sorry

/-- A column isomorphism induces an isomorphism on horizontal differential images. -/
@[stacks 015J "isomorphism on Cartan-Eilenberg column images"]
instance imageColumn_isIso (f : Map I J) (p : ℤ) [IsIso f.hom] :
    IsIso (imageColumn f p) := sorry

/-- A column isomorphism induces an isomorphism on horizontal homology. -/
@[stacks 015J "isomorphism on Cartan-Eilenberg column homology"]
instance homologyColumn_isIso (f : Map I J) (p : ℤ) [IsIso f.hom] :
    IsIso (homologyColumn f p) := sorry

/-- A row isomorphism induces an isomorphism on row cycles. -/
@[stacks 015J "isomorphism on Cartan-Eilenberg row cycles"]
instance cyclesRow_isIso (f : Map I J) (q p : ℤ) [IsIso f.hom] :
    IsIso (cyclesRow f q p) := sorry

/-- A row isomorphism induces an isomorphism on row differential images. -/
@[stacks 015J "isomorphism on Cartan-Eilenberg row images"]
instance imageRow_isIso (f : Map I J) (q p : ℤ) [IsIso f.hom] :
    IsIso (imageRow f q p) := sorry

/-- A row isomorphism induces an isomorphism on row homology. -/
@[stacks 015J "isomorphism on Cartan-Eilenberg row homology"]
instance homologyRow_isIso (f : Map I J) (q p : ℤ) [IsIso f.hom] :
    IsIso (homologyRow f q p) := sorry

end CochainComplex.CartanEilenbergResolution.Map
