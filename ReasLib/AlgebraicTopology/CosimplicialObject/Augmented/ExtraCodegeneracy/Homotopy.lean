/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Augmented.ExtraCodegeneracy
public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.Equiv

/-!
# Homotopy contraction from an extra codegeneracy

The canonical retraction of an extra codegeneracy is a product-free inverse to the
coaugmentation up to `DeltaOneHomotopic`. This leaf packages the two maps as the standard
cosimplicial `HomotopyEquiv`.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.CosimplicialObject.Augmented.ExtraCodegeneracy

variable {C : Type u} [Category.{v} C]
variable {X : CosimplicialObject.Augmented C} (ed : ExtraCodegeneracy X)

/-- The coaugmentation followed by the canonical retraction is product-free cosimplicially
homotopic to the identity. -/
@[stacks 0FKS "coaugmentation-retraction contraction from an extra codegeneracy"]
theorem hom_comp_retraction.homotopic_id :
    CosimplicialObject.DeltaOneHomotopic (X.hom ≫ ed.retraction)
      (𝟙 ((CosimplicialObject.const C).obj X.left)) := sorry

/-- The canonical retraction followed by the coaugmentation is product-free cosimplicially
homotopic to the identity. -/
@[stacks 0FKS "extra-codegeneracy contraction"]
theorem retraction_comp_hom.homotopic_id :
    CosimplicialObject.DeltaOneHomotopic (ed.retraction ≫ X.hom) (𝟙 X.right) := sorry

/-- An extra codegeneracy packages its coaugmentation and canonical retraction as a
cosimplicial homotopy equivalence. -/
@[stacks 0FKS "cosimplicial homotopy equivalence from an extra codegeneracy"]
def homotopyEquiv :
    CosimplicialObject.HomotopyEquiv
      ((CosimplicialObject.const C).obj X.left) X.right where
  hom := X.hom
  inv := ed.retraction
  hom_inv_id := hom_comp_retraction.homotopic_id ed
  inv_hom_id := retraction_comp_hom.homotopic_id ed

/-- The forward map of the homotopy equivalence supplied by an extra codegeneracy is the
coaugmentation. -/
@[simp, stacks 0FKS "forward map from an extra codegeneracy"]
theorem homotopyEquiv.hom : ed.homotopyEquiv.hom = X.hom := sorry

/-- The inverse map of the homotopy equivalence supplied by an extra codegeneracy is its
canonical retraction. -/
@[simp, stacks 0FKS "inverse map from an extra codegeneracy"]
theorem homotopyEquiv.inv : ed.homotopyEquiv.inv = ed.retraction := sorry

/-- The coaugmentation of an augmented cosimplicial object with an extra codegeneracy is a
product-free cosimplicial homotopy equivalence. -/
@[stacks 0FKS "coaugmentation with an extra codegeneracy is a homotopy equivalence"]
theorem isHomotopyEquivalence :
    CosimplicialObject.IsHomotopyEquivalence X.hom := sorry

end CategoryTheory.CosimplicialObject.Augmented.ExtraCodegeneracy
