/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- The quotient sheaf is the sheafification of the universe-raised objectwise quotient
presheaf. -/
#check (@AlgebraicGeometry.Scheme.PreRelation.quotientSheaf :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {U : Over S}
    (J : GrothendieckTopology (Over S)) (P : AlgebraicGeometry.Scheme.PreRelation U),
      Sheaf J (Type (u + 1)))

/- The quotient map sends the represented scheme to its quotient sheaf. -/
#check (@AlgebraicGeometry.Scheme.PreRelation.quotientMap :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {U : Over S}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical]
    (P : AlgebraicGeometry.Scheme.PreRelation U),
      J.uliftYoneda.{u + 1}.obj U ⟶ P.quotientSheaf J)

/- The represented relation maps canonically to the kernel pair of the quotient map. -/
#check (@AlgebraicGeometry.Scheme.PreRelation.relationToKernelPair :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {U : Over S}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical]
    (P : AlgebraicGeometry.Scheme.PreRelation U),
      J.uliftYoneda.{u + 1}.obj P.left ⟶ pullback (P.quotientMap J) (P.quotientMap J))
