/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic

/-! # Composition of total derived module pullbacks

The composition isomorphism for concrete derived pullbacks transports through the
canonical uniqueness isomorphisms to the total left derived functors.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Total derived module pullback along a composite is canonically isomorphic to
the composite of the total derived module pullbacks, in reverse order. -/
def totalPullbackCompIso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ Z) (g : Z ⟶ X) :
    Functor.LeftDerived.Homotopy.functor (Modules.pullback g) ⋙
        Functor.LeftDerived.Homotopy.functor (Modules.pullback f) ≅
      Functor.LeftDerived.Homotopy.functor (Modules.pullback (f ≫ g)) :=
  Functor.isoWhiskerLeft
      (Functor.LeftDerived.Homotopy.functor (Modules.pullback g))
      (ModuleDerived.pullbackIsoTotalLeftDerived f).symm ≪≫
    Functor.isoWhiskerRight (ModuleDerived.pullbackIsoTotalLeftDerived g).symm
      (ModuleDerived.pullback f) ≪≫
    ModuleDerived.pullbackCompIso f g ≪≫
    ModuleDerived.pullbackIsoTotalLeftDerived (f ≫ g)

/-- The canonical comparison from iterated total derived module pullback to
total derived module pullback along the composite morphism. -/
def totalPullbackCompComparison {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ Z) (g : Z ⟶ X) :
    Functor.LeftDerived.Homotopy.functor (Modules.pullback g) ⋙
        Functor.LeftDerived.Homotopy.functor (Modules.pullback f) ⟶
      Functor.LeftDerived.Homotopy.functor (Modules.pullback (f ≫ g)) :=
  (totalPullbackCompIso f g).hom

/-- The composition comparison of total derived module pullbacks is invertible
for arbitrary morphisms of algebraic spaces. -/
instance totalPullbackCompComparison_isIso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ Z) (g : Z ⟶ X) : IsIso (totalPullbackCompComparison f g) := by
  change IsIso (totalPullbackCompIso f g).hom
  infer_instance

/-- The transported composition comparison agrees with the canonical
total-left-derived composition comparison of module pullbacks. -/
theorem totalPullbackCompComparison_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ Z) (g : Z ⟶ X) :
    totalPullbackCompComparison f g =
      Functor.LeftDerived.Homotopy.Composition.comparison
        (Modules.pullback f) (Modules.pullback g) (Modules.pullback (f ≫ g))
        (Modules.pullbackCompIso f g).symm :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
