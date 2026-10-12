/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyCategory
public import ReasLib.CategoryTheory.Sites.Hypercovering.Category
public import ReasLib.CategoryTheory.Sites.Hypercovering.Refinement

/-!
# The homotopy category of fixed-target hypercoverings

Morphisms of fixed-target hypercoverings are identified when their underlying simplicial maps
are connected by zigzag simplicial homotopies.  This is the reusable index category underlying
hypercovering descent and hypercovering Cech cohomology.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Hypercovering

open CategoryTheory.Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {J : GrothendieckTopology C} {X : C}

/-- A morphism `c : K' ⟶ K` is a homotopy refinement of two maps `a, b : K ⟶ L` when
the two refined underlying simplicial maps are joined by one directed simplicial homotopy. -/
@[stacks 01GS "direct simplicial homotopy after hypercovering refinement"]
def IsHomotopyRefinement {K L : Hypercovering.{w} J X} (a b : K ⟶ L)
    {K' : Hypercovering.{w} J X} (c : K' ⟶ K) : Prop :=
  SimplicialObject.DirectedHomotopy
    (Hom.toSimplicial (c ≫ a)) (Hom.toSimplicial (c ≫ b))

/-- A homotopy refinement identifies the two refined maps under the zigzag homotopy relation. -/
theorem IsHomotopyRefinement.homotopic {K L : Hypercovering.{w} J X} {a b : K ⟶ L}
    {K' : Hypercovering.{w} J X} {c : K' ⟶ K} (h : IsHomotopyRefinement a b c) :
    SimplicialObject.Homotopic
      (Hom.toSimplicial (c ≫ a)) (Hom.toSimplicial (c ≫ b)) := sorry

/-- Lemma 25.9.2 (Tag 01GS): two morphisms between fixed-target hypercoverings become directly
simplicially homotopic after precomposition with a hypercovering refinement. -/
@[stacks 01GS "homotopy refinement of parallel hypercovering morphisms"]
theorem existsHomotopyRefinement
    {K L : Hypercovering.{w} J X} (a b : K ⟶ L) :
    ∃ (K' : Hypercovering.{w} J X) (c : K' ⟶ K),
      IsHomotopyRefinement a b c := sorry

/-- Section 25.10 (Tag 01GZ): the hom-set relation on fixed-target hypercoverings induced by
zigzag simplicial homotopy of the underlying maps. -/
@[stacks 01GZ "homotopy relation on fixed-target hypercoverings"]
def homotopyRel : HomRel (Hypercovering.{w} J X) :=
  fun _ _ f g => SimplicialObject.Homotopic (Hom.toSimplicial f) (Hom.toSimplicial g)

/-- Simplicial homotopy of hypercovering maps is compatible with identities and composition. -/
instance homotopyRelCongruence : Congruence (homotopyRel (J := J) (X := X)) := sorry

/-- Section 25.10 (Tag 01GZ): the category of fixed-target hypercoverings with morphisms taken
up to zigzag simplicial homotopy. -/
@[stacks 01GZ "homotopy category of fixed-target hypercoverings"]
def HomotopyCategory (J : GrothendieckTopology C) (X : C) :=
  CategoryTheory.Quotient (homotopyRel (J := J) (X := X))

/-- The quotient category inherits its category structure from `CategoryTheory.Quotient`. -/
instance homotopyCategoryInstCategory : Category (HomotopyCategory.{v, u, w} J X) :=
  inferInstanceAs <| Category
    (CategoryTheory.Quotient (homotopyRel (J := J) (X := X)))

namespace HomotopyCategory

/-- The canonical functor from fixed-target hypercoverings to their homotopy category. -/
@[stacks 01GZ "quotient functor for fixed-target hypercoverings"]
def quotient : Hypercovering.{w} J X ⥤ HomotopyCategory.{v, u, w} J X :=
  CategoryTheory.Quotient.functor (homotopyRel (J := J) (X := X))

/-- Two hypercovering morphisms have the same homotopy-class image exactly when their
underlying simplicial maps are homotopic. -/
theorem quotient_map_eq_iff {K L : Hypercovering.{w} J X} (f g : K ⟶ L) :
    (quotient (J := J) (X := X)).map f = (quotient (J := J) (X := X)).map g ↔
      SimplicialObject.Homotopic (Hom.toSimplicial f) (Hom.toSimplicial g) := sorry

/-- Homotopic hypercovering maps have equal images under the quotient functor. -/
theorem quotient_map_eq_of_homotopic {K L : Hypercovering.{w} J X} (f g : K ⟶ L)
    (h : SimplicialObject.Homotopic (Hom.toSimplicial f) (Hom.toSimplicial g)) :
    (quotient (J := J) (X := X)).map f =
      (quotient (J := J) (X := X)).map g := sorry

/-- A homotopy refinement makes the two refined maps equal in the hypercovering homotopy
category. -/
theorem quotient_map_eq_of_refinement {K L : Hypercovering.{w} J X} {a b : K ⟶ L}
    {K' : Hypercovering.{w} J X} {c : K' ⟶ K} (h : IsHomotopyRefinement a b c) :
    (quotient (J := J) (X := X)).map (c ≫ a) =
      (quotient (J := J) (X := X)).map (c ≫ b) := sorry

/-- Every morphism in the hypercovering homotopy category has a representative. -/
instance quotientFull : (quotient (J := J) (X := X)).Full := sorry

/-- Every object of the hypercovering homotopy category is represented by a hypercovering. -/
instance quotientEssSurj : (quotient (J := J) (X := X)).EssSurj := sorry

end HomotopyCategory

end CategoryTheory.Hypercovering
