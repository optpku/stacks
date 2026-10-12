/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.OfPresheaf
public import stacks_project.Chap87.Definition_87_9_9_Spf
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import ReasLib.RingTheory.Topology.Adic.Complete

/-!
# The category fibred in groupoids associated to Spf(A)

The fppf functor `X = Spf(A)` determines a category fibred in sets by the discrete
Grothendieck construction of Categories, Example 4.38.5, and we forget from sets to
groupoids so that `QC` applies.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The category fibred in groupoids associated to the fppf functor `Spf(A)`. -/
def spfToGroupoids (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    GroupoidsOver S :=
  (Sets.toGroupoids (Over S)).obj
    ((Sets.ofPresheaf (Over S)).obj (spf A structureHom).obj)

/-- `spfToGroupoids A structureHom` is the discrete Grothendieck construction of
`Spf(A)`, forgotten from categories fibred in sets to categories fibred in groupoids. -/
theorem spfToGroupoids_eq (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    spfToGroupoids A structureHom =
      (Sets.toGroupoids (Over S)).obj
        ((Sets.ofPresheaf (Over S)).obj (spf A structureHom).obj) :=
  sorry

/-- The projection of `spfToGroupoids A structureHom` is the opposite
category-of-elements projection of the underlying presheaf of `Spf(A)`. -/
theorem spfToGroupoids_p (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    (spfToGroupoids A structureHom).p =
      (CategoryOfElements.π (spf A structureHom).obj).leftOp :=
  sorry

end AlgebraicGeometry.GroupoidsOver
