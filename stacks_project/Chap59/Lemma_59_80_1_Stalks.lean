/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.StrictHenselian

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

#check (AlgebraicGeometry.Scheme.HasStrictlyHenselianStalks : Scheme.{u} → Prop)

#check (AlgebraicGeometry.Scheme.HasStrictlyHenselianStalks.spec :
  ∀ (S : Scheme.{u}) [HasStrictlyHenselianStalks S] (x : S),
    StrictHenselianLocalRing (S.presheaf.stalk x))

#check (AlgebraicGeometry.Scheme.instHasStrictlyHenselianStalks_of_strictHenselianLocalRing :
  ∀ {R : Type u} [CommRing R] [StrictHenselianLocalRing R],
    HasStrictlyHenselianStalks (Spec (.of R)))

end AlgebraicGeometry.Scheme
