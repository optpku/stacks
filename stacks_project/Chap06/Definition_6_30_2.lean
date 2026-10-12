/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.Basis.Cover
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

variable {X : Type u} [TopologicalSpace X]
variable {B : Set (Opens X)}
variable (F : (BasisOpen B)ᵒᵖ ⥤ Type v)

/-
The reusable predicate is defined for arbitrary collections of opens in `BasisSheaf`. The source
specializes it to a topological basis.
-/
/- Definition 6.30.2 (1): a set-valued presheaf on a topological basis is a sheaf when every
compatible family on a basis cover, tested on basis covers of pairwise intersections, has a
unique amalgamation. -/
@[stacks 009J "the basis-cover gluing condition for a presheaf of sets"]
#check (Presheaf.IsBasisSheaf F)

/- Definition 6.30.2 (2): sheaves of sets on `B`, with presheaf morphisms as morphisms, form the
full subcategory `BasisSheaf B`. -/
@[stacks 009J "morphisms of basis sheaves are morphisms of the underlying presheaves"]
#check (BasisSheaf.{u, v} B)
