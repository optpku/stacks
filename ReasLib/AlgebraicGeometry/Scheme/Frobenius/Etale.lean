/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.WeaklyEtale

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The relative Frobenius of an étale morphism in prime characteristic is an
isomorphism. -/
theorem relativeFrobenius_isIso_of_etale {p : ℕ} [Fact p.Prime] {U X : Scheme.{u}}
    (f : U ⟶ X) [Scheme.IsCharP X p] [Etale f] :
    IsIso (relativeFrobenius (p := p) f) :=
  relativeFrobenius_isIso (p := p) f

end AlgebraicGeometry.Scheme.Hom
