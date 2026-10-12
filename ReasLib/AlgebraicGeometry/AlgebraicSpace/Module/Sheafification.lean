/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Modules
public import ReasLib.CategoryTheory.Sites.Over.SheafCompose
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale

/-- Abelian-group-valued presheaves on the small étale site admit left exact
sheafification in the coefficient universe. -/
instance hasSheafify {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasSheafify (topology X) AddCommGrpCat.{u} := sorry

/-- A morphism of abelian-group-valued presheaves on the small étale site becomes an
isomorphism after sheafification exactly when it is locally bijective. -/
instance wEqualsLocallyBijective {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (topology X).WEqualsLocallyBijective AddCommGrpCat.{u} := sorry

/-- Abelian-group-valued presheaves on each slice of the small étale site admit left
exact sheafification in the coefficient universe. -/
instance overHasSheafify {S : Scheme.{u}} (X : AlgebraicSpace S) (U : site X) :
    HasSheafify ((topology X).over U) AddCommGrpCat.{u} := sorry

/-- A morphism of abelian-group-valued presheaves on a slice of the small étale site
becomes an isomorphism after sheafification exactly when it is locally bijective. -/
instance overWEqualsLocallyBijective {S : Scheme.{u}} (X : AlgebraicSpace S) (U : site X) :
    ((topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u} := sorry

/-- Forgetting rings to abelian groups preserves the sheaf condition on the small
étale site. -/
instance hasSheafComposeForget {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (topology X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u}) := sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtale
