module

public import ReasLib.Topology.Sheaves.Basis.Cofinal
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

variable {X : Type u} [TopologicalSpace X] {B : Set (Opens X)}

/- Lemma 6.30.4: if intersections of basis opens below a common basis open remain in the basis,
a presheaf of sets is a sheaf on the basis if and only if every compatible family on every cover
in a chosen cofinal system has a unique amalgamation. -/
@[stacks 009L]
#check
  CategoryTheory.Presheaf.isBasisSheaf_iff_uniqueGluing_on_cofinalCovers
    (X := X) (B := B)
