/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.Etale
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType

/-!
# Étale morphisms are locally of finite type

An étale morphism of functors of points is locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- An étale morphism of functors of points is locally of finite type. -/
instance locallyOfFiniteType_of_etale {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) [Etale f] : LocallyOfFiniteType f :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
