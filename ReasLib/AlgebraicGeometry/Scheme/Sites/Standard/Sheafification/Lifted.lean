/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Sheafification

/-!
# Lifted-universe sheafification on standard scheme sites

This module supplies weak sheafification and local-bijection instances at the
coefficient universe used by commutative presentations of module sheaves.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.StandardTopology.Big

/-- Weak sheafification at the lifted coefficient universe exists on every
standard big scheme site. -/
instance instCommHasWeakSheafify (τ : StandardTopology) (S : Scheme.{u}) :
    HasWeakSheafify (τ.overTopology S) AddCommGrpCat.{u + 1} := sorry

/-- At the lifted coefficient universe, sheafification equivalences on every
standard big scheme site are exactly the locally bijective morphisms. -/
instance instCommWEqualsLocallyBijective
    (τ : StandardTopology) (S : Scheme.{u}) :
    (τ.overTopology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := sorry

/-- Weak sheafification at the lifted coefficient universe exists on every
slice of a standard big scheme site. -/
instance instCommHasWeakSheafifyOver
    (τ : StandardTopology) (S : Scheme.{u}) :
    ∀ U : Over S,
      HasWeakSheafify ((τ.overTopology S).over U) AddCommGrpCat.{u + 1} := sorry

/-- At the lifted coefficient universe, sheafification equivalences on every
slice of a standard big scheme site are exactly the locally bijective morphisms. -/
instance instCommWEqualsLocallyBijectiveOver
    (τ : StandardTopology) (S : Scheme.{u}) :
    ∀ U : Over S,
      ((τ.overTopology S).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u + 1} := sorry

end AlgebraicGeometry.StandardTopology.Big

namespace AlgebraicGeometry.StandardTopology.Small

/-- Weak sheafification at the lifted coefficient universe exists on every
slice of a small standard scheme site. -/
instance instCommHasWeakSheafifyOver
    (τ : StandardTopology) (S : Scheme.{u}) :
    ∀ U : site τ S,
      HasWeakSheafify ((topology τ S).over U) AddCommGrpCat.{u + 1} := sorry

/-- At the lifted coefficient universe, sheafification equivalences on every
slice of a small standard scheme site are exactly the locally bijective morphisms. -/
instance instCommWEqualsLocallyBijectiveOver
    (τ : StandardTopology) (S : Scheme.{u}) :
    ∀ U : site τ S,
      ((topology τ S).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u + 1} := sorry

end AlgebraicGeometry.StandardTopology.Small
