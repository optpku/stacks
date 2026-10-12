/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Lemma_85_27_5_Equivalence

/-!
# Lemma 85.27.5

The construction of Lemma 85.27.4, sending cartesian simplicial schemes over the
Čech nerve of `f : X ⟶ S` to descent data relative to `X / S`, is an equivalence
of categories.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped Simplicial
open CategoryTheory.SimplicialObject

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.DescentData

/-- Lemma 85.27.5: let `f : X ⟶ S` be a morphism of schemes. The construction of
Lemma 85.27.4 sending the category of cartesian schemes over `f.simplicialScheme`
to the category of descent data relative to `X / S` is an equivalence of
categories. -/
@[stacks 024C]
def ofCartesianOverEquivalence {X S : Scheme.{u}} (f : X ⟶ S) :
    CartesianOver f.simplicialScheme ≌
      DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f) :=
  CategoryTheory.Equivalence.mk (ofCartesianOverFunctor f) (ofCartesianOverInverse f)
    (ofCartesianOverUnitIso f) (ofCartesianOverCounitIso f)

/-- The forward functor of `ofCartesianOverEquivalence f` is `ofCartesianOverFunctor f`. -/
theorem ofCartesianOverEquivalence_functor {X S : Scheme.{u}} (f : X ⟶ S) :
    (ofCartesianOverEquivalence f).functor = ofCartesianOverFunctor f := sorry

/-- The inverse functor of `ofCartesianOverEquivalence f` is `ofCartesianOverInverse f`. -/
theorem ofCartesianOverEquivalence_inverse {X S : Scheme.{u}} (f : X ⟶ S) :
    (ofCartesianOverEquivalence f).inverse = ofCartesianOverInverse f := sorry

/-- On objects, the forward functor of `ofCartesianOverEquivalence f` is the
construction `ofCartesianOver f` of Lemma 85.27.4. -/
theorem ofCartesianOverEquivalence_functor_obj {X S : Scheme.{u}} (f : X ⟶ S)
    (Y : CartesianOver f.simplicialScheme) :
    (ofCartesianOverEquivalence f).functor.obj Y = ofCartesianOver f Y := sorry

end AlgebraicGeometry.Scheme.DescentData
