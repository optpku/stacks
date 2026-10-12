/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.LocalEquality

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor

/-- Pullback to singleton étale descent data along a surjective scheme morphism is faithful. -/
@[stacks 0BTJ]
instance faithful_of_surjective {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f] :
    (canonicalFunctor f).Faithful := sorry

end AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor
