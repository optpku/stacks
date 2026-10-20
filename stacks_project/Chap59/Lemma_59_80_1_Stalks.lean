/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
