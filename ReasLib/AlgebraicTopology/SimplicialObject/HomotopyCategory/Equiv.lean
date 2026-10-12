/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyCategory
public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 019N

# Homotopy equivalences and the simplicial homotopy category

This file relates structured simplicial homotopy equivalences to isomorphisms in the quotient
by simplicial homotopy.  It is kept separate from both underlying owners so that neither the
relation nor its structured equivalences depend on the specialized quotient category.
-/

@[expose] public section

universe u v

namespace CategoryTheory.SimplicialObject.HomotopyCategory

variable {C : Type u} [Category.{v} C]
variable {U V : SimplicialObject C}

/-- A simplicial homotopy equivalence induces an isomorphism in the simplicial homotopy
category. -/
@[stacks 019N "homotopy equivalence gives an isomorphism in the homotopy category"]
def isoOfEquiv (e : HomotopyEquiv U V) :
    (quotient C).obj U ≅ (quotient C).obj V :=
  e.toIso

namespace isoOfEquiv

/-- The forward map of the homotopy-category isomorphism induced by a homotopy equivalence. -/
@[simp, stacks 019N "forward map of the induced homotopy-category isomorphism"]
theorem hom (e : HomotopyEquiv U V) :
    (isoOfEquiv e).hom = (quotient C).map e.hom := sorry

/-- The inverse map of the homotopy-category isomorphism induced by a homotopy equivalence. -/
@[simp, stacks 019N "inverse map of the induced homotopy-category isomorphism"]
theorem inv (e : HomotopyEquiv U V) :
    (isoOfEquiv e).inv = (quotient C).map e.inv := sorry

end isoOfEquiv

/-- An isomorphism between images in the simplicial homotopy category determines a simplicial
homotopy equivalence. -/
@[stacks 019N "homotopy-category isomorphism gives a homotopy equivalence"]
noncomputable def equivOfIso (e : (quotient C).obj U ≅ (quotient C).obj V) :
    HomotopyEquiv U V :=
  HomRel.Equiv.ofQuotientIso e

namespace equivOfIso

/-- The chosen forward map of `equivOfIso e` maps to the forward map of `e`. -/
@[stacks 019N "forward-map specification for homotopy-category isomorphisms"]
theorem hom_map (e : (quotient C).obj U ≅ (quotient C).obj V) :
    (quotient C).map (equivOfIso e).hom = e.hom := sorry

/-- The chosen inverse map of `equivOfIso e` maps to the inverse map of `e`. -/
@[stacks 019N "inverse-map specification for homotopy-category isomorphisms"]
theorem inv_map (e : (quotient C).obj U ≅ (quotient C).obj V) :
    (quotient C).map (equivOfIso e).inv = e.inv := sorry

/-- Passing from a homotopy-category isomorphism to chosen homotopy-equivalence data and back
recovers the original isomorphism. -/
@[simp, stacks 019N "round trip from a homotopy-category isomorphism"]
theorem isoOfEquiv (e : (quotient C).obj U ≅ (quotient C).obj V) :
    isoOfEquiv (equivOfIso e) = e := sorry

end equivOfIso

/-- Simplicial homotopy equivalences are exactly the inverse image of isomorphisms under the
quotient functor. -/
@[stacks 019N "homotopy equivalences as inverse images of quotient isomorphisms"]
theorem quotient.inverseImage_isomorphisms (C : Type u) [Category.{v} C] :
    (MorphismProperty.isomorphisms (HomotopyCategory C)).inverseImage (quotient C) =
      homotopyEquivalences C := sorry

namespace quotient

/-- A simplicial map becomes an isomorphism in the homotopy category exactly when it is a
simplicial homotopy equivalence. -/
@[stacks 019N "isomorphism criterion in the simplicial homotopy category"]
theorem isIso_map_iff {X Y : SimplicialObject C} (f : X ⟶ Y) :
    IsIso ((quotient C).map f) ↔ IsHomotopyEquivalence f := sorry

end quotient

end CategoryTheory.SimplicialObject.HomotopyCategory
