/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.QuasiFinite

/-!
# Étale morphisms of algebraic spaces are locally quasi-finite
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An étale morphism of algebraic spaces is locally quasi-finite. -/
instance locallyQuasiFinite_of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] : LocallyQuasiFinite f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
