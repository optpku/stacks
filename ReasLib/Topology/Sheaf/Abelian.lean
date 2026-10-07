module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import ReasLib.Topology.Sheaves.Abelian
public import ReasLib.Topology.Sheaf.Zero

/-!
# Abelian structure on sheaf categories

Re-exports the abelian-category structure on sheaves, together with the canonical homology
structure carried by every abelian category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w v u

namespace TopCat.Sheaf

variable {C : Type u} [Category.{v} C]
variable {X : TopCat.{w}}

/-- Sheaves valued in an abelian category carry the canonical homology structure. This named
instance fixes the universe parameters hidden by the `TopCat.Sheaf` abbreviation. -/
instance categoryWithHomology [Abelian (X.Sheaf C)] [HasZeroMorphisms (X.Sheaf C)] :
    CategoryWithHomology (X.Sheaf C) := sorry

end TopCat.Sheaf
