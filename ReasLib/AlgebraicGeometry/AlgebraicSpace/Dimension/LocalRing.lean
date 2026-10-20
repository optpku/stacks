module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Order.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Dimension.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Sober

/-!
# Dimension of local rings of algebraic spaces

The dimension of the local ring of an algebraic space at a point is the common Krull dimension
of the stalks of étale scheme charts through that point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The dimension of the local ring of an algebraic space at a point, as the supremum of the
Krull dimensions of stalks of étale scheme charts through that point. -/
noncomputable def localRingDimAt {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    WithBot ℕ∞ :=
  ⨆ (U : Over S) (f : ofOver U ⟶ X) (u : U.left)
    (_hf : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f)
    (_hx : Points.mapOfOver f u = x), ringKrullDim (U.left.presheaf.stalk u)

/-- The dimension of the local ring at a point equals the Krull dimension of the stalk of any
étale scheme chart through that point. -/
theorem localRingDimAt_eq_ringKrullDim_stalk {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} (f : ofOver U ⟶ X)
    (hf : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f) (u : U.left)
    {x : Points X} (hx : Points.mapOfOver f u = x) :
    localRingDimAt x = ringKrullDim (U.left.presheaf.stalk u) :=
  sorry

/-- The dimension of the local ring of an algebraic space at a point is nonnegative. -/
theorem localRingDimAt_nonneg {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    0 ≤ localRingDimAt x :=
  sorry

/-- On a scheme, viewed as an algebraic space, the dimension of the local ring at the image of a
point is the usual stalk Krull dimension. -/
theorem localRingDimAt_ofOver {S : Scheme.{u}} (T : Over S) (t : T.left) :
    localRingDimAt (ofOver.pointsEquiv T t) = ringKrullDim (T.left.presheaf.stalk t) :=
  sorry

/-- The dimension of an algebraic space is the supremum of the dimensions of its local rings. -/
theorem dimension_eq_iSup_localRingDimAt {S : Scheme.{u}} (X : AlgebraicSpace S) :
    dimension X = ⨆ x : Points X, localRingDimAt x :=
  sorry

/-- The dimension of the local ring at a generic point of an irreducible closed subset of a
decent algebraic space equals the coheight of that subset. -/
@[stacks 0ED1]
theorem localRingDimAt_eq_coheight {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (T : IrreducibleCloseds (Points X)) (ξ : Points X) (hξ : IsGenericPoint ξ T) :
    localRingDimAt ξ = Order.coheight T :=
  sorry

/-- The dimension of the local ring at the chosen generic point of an irreducible closed
subset of a decent algebraic space equals the coheight of that subset. -/
theorem localRingDimAt_genericPoint_eq_coheight {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (T : IrreducibleCloseds (Points X)) :
    localRingDimAt T.isIrreducible.genericPoint = Order.coheight T :=
  localRingDimAt_eq_coheight T T.isIrreducible.genericPoint
    (T.isIrreducible.isGenericPoint_genericPoint T.isClosed)

/-- The dimension of the local ring at a generic point of a raw irreducible closed subset of
a decent algebraic space equals the coheight of the associated irreducible closed subset. -/
theorem localRingDimAt_eq_coheight_mk {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {T : Set (Points X)} (hT_irred : IsIrreducible T) (hT_closed : IsClosed T)
    (ξ : Points X) (hξ : IsGenericPoint ξ T) :
    localRingDimAt ξ = Order.coheight (IrreducibleCloseds.mk T hT_irred hT_closed) :=
  localRingDimAt_eq_coheight (IrreducibleCloseds.mk T hT_irred hT_closed) ξ hξ

end AlgebraicGeometry.AlgebraicSpace
