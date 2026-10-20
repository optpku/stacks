module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.SpecStalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.RelationFiniteFibre
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.WeaklyAssociatedPoints

/-! # Pointed open scheme charts and their stalk spectra -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A pointed scheme over the base with an open immersion into an algebraic space. -/
structure OpenImmersionChart {S : Scheme.{u}} (X : AlgebraicSpace S) where
  /-- The source scheme over the base. -/
  U : Over S
  /-- The chart morphism. -/
  ι : ofOver U ⟶ X
  /-- The marked point of the chart. -/
  u : U.left
  /-- The chart morphism is an open immersion. -/
  isOpenImmersion : IsOpenImmersion ι

namespace OpenImmersionChart

/-- The spectrum of the local ring at the marked point, viewed over the base scheme. -/
def stalkOver {S : Scheme.{u}} {X : AlgebraicSpace S} (c : OpenImmersionChart X) : Over S :=
  specStalkOver c.U c.u

/-- The stalk spectrum of a pointed chart is the spectrum of its marked scheme stalk. -/
theorem stalkOver_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (c : OpenImmersionChart X) :
    c.stalkOver = specStalkOver c.U c.u :=
  rfl

/-- The canonical map from the spectrum of the marked local ring into the algebraic space. -/
def stalkMap {S : Scheme.{u}} {X : AlgebraicSpace S} (c : OpenImmersionChart X) :
    ofOver c.stalkOver ⟶ X :=
  fromSpecStalk c.ι c.u

/-- The canonical stalk map is the scheme stalk map followed by the chart morphism. -/
theorem stalkMap_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (c : OpenImmersionChart X) :
    c.stalkMap = fromSpecStalk c.ι c.u :=
  rfl

end OpenImmersionChart

/-- If weakly associated points have codimension zero, irreducible components are finite on
compact étale opens, and codimension-zero points have monomorphic field representatives,
then every codimension-zero point lies on a pointed open scheme chart. -/
theorem exists_isOpenImmersion_chart_of_mem_codimZero {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (η : codimZeroPoints X) :
    ∃ c : OpenImmersionChart X, Points.mapOfOver c.ι c.u = η :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
