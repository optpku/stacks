/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.Basis.Comparison
public import Mathlib.CategoryTheory.Whiskering

/-!
# Restriction of set-valued sheaves to a topological basis

The explicit restriction functor is sectionwise precomposition with `basisOpenInclusion B`; it is
kept alongside the dense-subsite comparison equivalence because this definitional presentation is
useful for section-level arguments.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

variable {X : TopCat.{u}} {B : Set (Opens X)}

namespace BasisSheaf

/-- Restricting a set-valued sheaf to the members of a topological basis satisfies the explicit
basis-cover sheaf condition. -/
theorem restrictionPresheaf_isBasisSheaf (hB : Opens.IsBasis B)
    (F : TopCat.Sheaf (Type (max u v)) X) :
    Presheaf.IsBasisSheaf ((basisOpenInclusion B).op ⋙ F.presheaf) := sorry

/-- The inverse of the canonical basis-sheaf comparison has underlying presheaf given by literal
restriction along the inclusion of basis opens. -/
theorem comparisonInverse_obj (hB : Opens.IsBasis B)
    (F : TopCat.Sheaf (Type (max u v)) X) :
    ((basisSheafComparisonEquiv hB).inverse.obj F).obj =
      (basisOpenInclusion B).op ⋙ F.presheaf := sorry

/-- Restriction of set-valued sheaves on `X` to sheaves on the topological basis `B`. -/
def restriction (hB : Opens.IsBasis B) :
    TopCat.Sheaf (Type (max u v)) X ⥤ BasisSheaf B where
  obj F :=
    ⟨(basisOpenInclusion B).op ⋙ F.presheaf,
      restrictionPresheaf_isBasisSheaf hB F⟩
  map f := ObjectProperty.homMk
    (Functor.whiskerLeft (basisOpenInclusion B).op f.hom)

/-- Restriction from set-valued sheaves on a space to sheaves on a topological basis is an
equivalence. -/
@[stacks 009O "restriction to a basis is an equivalence of categories"]
instance restriction_isEquivalence (hB : Opens.IsBasis B) :
    (restriction hB).IsEquivalence := sorry

end BasisSheaf
