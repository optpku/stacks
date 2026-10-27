/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.IsolatedSingularities
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.DeligneMumford
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Smooth

/-!
# Local complete intersection curves with isolated singularities

The intersection of the local complete intersection and isolated-singularities
loci of curve families is an open substack smooth over the base scheme.
Membership is characterized by local complete intersection and finiteness of
the singular locus; over a field it is characterized by finitely many
nonsmooth points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The intersection of the local complete intersection and isolated-singularities
object properties of families of curves. -/
def lciPlus (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ lci S P ∧ isolatedSingularities S P

/-- A curve family belongs to the intersection locus precisely when its structure
morphism is a local complete intersection with isolated singularities. -/
theorem lciPlus_iff {S : Scheme.{u}} (P : Obj S) :
    lciPlus S P ↔
      AlgebraicSpace.IsLocalCompleteIntersection (hom P) ∧
        IsolatedSingularities (hom P) :=
  Iff.rfl

/-- The local complete intersection and isolated-singularities intersection
property of curve families is invariant under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_lciPlus (S : Scheme.{u}) :
    (lciPlus S).IsClosedUnderIsomorphisms :=
  sorry

/-- A curve family in the intersection locus has a local complete intersection
structure morphism. -/
theorem lciPlus_isLocalCompleteIntersection {S : Scheme.{u}} {P : Obj S}
    (h : lciPlus S P) : AlgebraicSpace.IsLocalCompleteIntersection (hom P) :=
  h.1

/-- A curve family in the intersection locus has isolated singularities. -/
theorem lciPlus_isolatedSingularities {S : Scheme.{u}} {P : Obj S}
    (h : lciPlus S P) : IsolatedSingularities (hom P) :=
  h.2

/-- Curve families that are local complete intersections with isolated
singularities form a category fibred in groupoids over the base schemes. -/
instance instIsFiberedInGroupoids_lciPlus (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((lciPlus S).ι ⋙ p S) :=
  sorry

/-- The inclusion of the local complete intersection and isolated-singularities
locus into the stack of curves is an open immersion. -/
instance instOpenImmersion_inclusionOf_lciPlus (S : Scheme.{u}) :
    CohStack.OpenImmersion (inclusionOf (lciPlus S)) :=
  sorry

/-- The structure morphism of the stack of local complete intersection curves
with isolated singularities is smooth over every base scheme. -/
instance instSmooth_lciPlus (S : Scheme.{u}) :
    CohStack.Hom.Smooth
      (inclusionOf (lciPlus S) ≫ CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

/-- A curve family is classified by the local complete intersection and
isolated-singularities locus precisely when its structure morphism is a local
complete intersection and every closed subspace structure on its nonsmooth
locus is finite over the base. -/
theorem classifying_factorsThrough_lciPlus_iff {S : Scheme.{u}} (P : Obj S) :
    lciPlus S P ↔
      AlgebraicSpace.IsLocalCompleteIntersection (hom P) ∧
        ∀ T : ClosedSubspaceStructure (nonsmoothLocusClosed (hom P)),
          IsFinite (T.ι ≫ hom P) :=
  sorry

/-- A proper scheme of dimension at most one over a field belongs to the local
complete intersection and isolated-singularities locus precisely when it is
a local complete intersection over the field and has finitely many nonsmooth
points. -/
theorem classifying_factorsThrough_lciPlus_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    lciPlus (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      IsLocalCompleteIntersectionOver k X.hom ∧
        Set.Finite (setOf fun x : X.left ↦ ¬ X.hom.SmoothAt x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
