/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.CategoryTheory.Fibered.FullSubcategory.Stack
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.MorphismProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.OpenImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Algebraic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Automorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.OverField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically.Reduced
public import Mathlib.Data.List.TFAE

/-!
# The object property of DM families of curves

`𝒞urves^{DM}` is the full subcategory of families of curves whose automorphism
algebraic space is unramified over the base. An object property of families is
an open DM substack of `𝒞urves` when the corresponding full subcategory of
`toGroupoids` is a cartesian algebraic stack, the inclusion is an open
immersion, and the object diagonal is unramified.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The full subcategory of families of curves cut out by `Q`, as a category
fibred in groupoids over `Over S` at the Hom-universe of `toGroupoids`. -/
def ofObjectProperty {S : Scheme.{u}} (Q : ObjectProperty (Obj S))
    [Functor.IsFibered.InGroupoids (Q.ι ⋙ p S)] :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1} (Q.ι ⋙ p S)

/-- The projection of `ofObjectProperty Q` is the restricted forgetful functor. -/
theorem ofObjectProperty_p {S : Scheme.{u}} (Q : ObjectProperty (Obj S))
    [Functor.IsFibered.InGroupoids (Q.ι ⋙ p S)] :
    (ofObjectProperty Q).p = Q.ι ⋙ p S :=
  rfl

/-- The inclusion of the full subcategory cut out by `Q` into `𝒞urves`, as a
1-morphism of categories fibred in groupoids over `Over S`. -/
def inclusionOf {S : Scheme.{u}} (Q : ObjectProperty (Obj S))
    [Functor.IsFibered.InGroupoids (Q.ι ⋙ p S)] :
    ofObjectProperty Q ⟶ toGroupoids S :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    { toFunctor := Q.ι
      w := rfl }

/-- The underlying functor of `inclusionOf Q` is the full-subcategory inclusion. -/
theorem inclusionOf_toFunctor {S : Scheme.{u}} (Q : ObjectProperty (Obj S))
    [Functor.IsFibered.InGroupoids (Q.ι ⋙ p S)] :
    FiberedCategoryOver.Groupoids.toFunctor (inclusionOf Q) = Q.ι :=
  rfl

/-- An object property of families of curves cuts out an open DM substack of
`𝒞urves` when the corresponding full subcategory of `toGroupoids` is cartesian
and algebraic, the inclusion is an open immersion, and the object diagonal is
unramified. -/
class IsOpenDMSubstack {S : Scheme.{u}} (Q : ObjectProperty (Obj S)) : Prop where
  /-- The property is stable under strongly cartesian pullback. -/
  cartesian : IsStableUnder.CartesianPullback Q (p S)
  /-- The full subcategory remains fibred in groupoids over `Over S`. -/
  isFiberedInGroupoids : Functor.IsFibered.InGroupoids (Q.ι ⋙ p S)
  /-- The full subcategory is an algebraic stack in the Hom-universe of
  `toGroupoids`. -/
  isAlgebraicStack :
    CohStack.AlgebraicStack (@ofObjectProperty S Q isFiberedInGroupoids)
  /-- The inclusion into `𝒞urves` is an open immersion. -/
  isOpenImmersion :
    CohStack.OpenImmersion (@inclusionOf S Q isFiberedInGroupoids)
  /-- The object diagonal of the full subcategory is unramified. -/
  unramified_diagonal :
    CohStack.Hom.has (@AlgebraicSpace.Unramified S)
      (CohStack.diagonal (@ofObjectProperty S Q isFiberedInGroupoids))

/-- A full subcategory cut out by an open DM substack remains fibred in
groupoids. -/
instance instIsFiberedInGroupoids_isOpenDMSubstack {S : Scheme.{u}}
    (Q : ObjectProperty ((relativeDimensionLE S 1).FullSubcategory))
    [h : IsOpenDMSubstack Q] :
    Functor.IsFibered.InGroupoids (Q.ι ⋙ p S) :=
  h.isFiberedInGroupoids

/-- The full subcategory cut out by an open DM substack is an algebraic stack. -/
instance instAlgebraicStack_isOpenDMSubstack {S : Scheme.{u}}
    (Q : ObjectProperty ((relativeDimensionLE S 1).FullSubcategory))
    [h : IsOpenDMSubstack Q] :
    CohStack.AlgebraicStack (ofObjectProperty Q) :=
  h.isAlgebraicStack

/-- The inclusion of an open DM substack into `𝒞urves` is an open immersion. -/
instance instOpenImmersion_isOpenDMSubstack {S : Scheme.{u}}
    (Q : ObjectProperty ((relativeDimensionLE S 1).FullSubcategory))
    [h : IsOpenDMSubstack Q] :
    CohStack.OpenImmersion (inclusionOf Q) :=
  h.isOpenImmersion

/-- The defining conditions of an open DM substack of `𝒞urves`: cartesian
pullback stability, a groupoid fibration, an algebraic stack, an open
immersion into `toGroupoids`, and an unramified object diagonal. -/
theorem IsOpenDMSubstack.spec {S : Scheme.{u}} (Q : ObjectProperty (Obj S))
    [h : IsOpenDMSubstack Q] :
    IsStableUnder.CartesianPullback Q (p S) ∧
      Functor.IsFibered.InGroupoids (Q.ι ⋙ p S) ∧
      CohStack.AlgebraicStack (ofObjectProperty Q) ∧
      CohStack.OpenImmersion (inclusionOf Q) ∧
      CohStack.Hom.has (@AlgebraicSpace.Unramified S)
        (CohStack.diagonal (ofObjectProperty Q)) :=
  sorry

/-- The object property of families of curves with unramified automorphism
algebraic space, corresponding to the open substack `𝒞urves^{DM}`. -/
def dm (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ IsUnramified P

/-- Membership in `dm` means the automorphism algebraic space of the family is
unramified over the base. -/
theorem dm_iff {S : Scheme.{u}} (P : Obj S) :
    dm S P ↔ IsUnramified P :=
  Iff.rfl

/-- The DM property of families of curves is closed under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_dm (S : Scheme.{u}) :
    (dm S).IsClosedUnderIsomorphisms :=
  sorry

/-- `𝒞urves^{DM}` is an open DM substack of `𝒞urves`. -/
instance instIsOpenDMSubstack_dm (S : Scheme.{u}) :
    IsOpenDMSubstack (dm S) :=
  sorry

/-- Every open Deligne–Mumford substack of families of curves is contained in
 the locus of families with unramified automorphism algebraic space. -/
theorem dm_isLargest {S : Scheme.{u}} (Q : ObjectProperty (Obj S))
    [IsOpenDMSubstack Q] : Q ≤ dm S :=
  sorry

/-- For a proper scheme of dimension at most one over a field, membership in
 the Deligne–Mumford locus is equivalent to geometric reducedness and dimension
 zero of its automorphism space, and to unramifiedness of that space. -/
theorem classifying_factorsThrough_dm_tfae_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    List.TFAE
      [dm (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim),
        (∀ G : AlgebraicSpace (Spec (CommRingCat.of k)),
          IsRepresentedBy (mkOfSchemeOverField X hdim) G →
            GeometricallyReduced G ∧ dimension G = 0),
        IsUnramified (mkOfSchemeOverField X hdim)] :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
