module

public import stacks_project.Chap75.Lemma_75_11_2_Coherator
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward

/-! # Derived module pushforward on algebraic spaces

Typed compatibility checks for the unbounded derived direct image and its
canonical cochain comparison and universal property.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

#check (AlgebraicGeometry.AlgebraicSpace.Modules.moduleDerivedPushforward :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y),
    ModuleDerived X ⥤ ModuleDerived Y)

namespace moduleDerivedPushforward

#check (AlgebraicGeometry.AlgebraicSpace.Modules.moduleDerivedPushforward.unit :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    (pushforward f).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ DerivedCategory (Modules Y)) ⟶
      (DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ DerivedCategory (Modules X)) ⋙
        moduleDerivedPushforward f)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.moduleDerivedPushforward.isRightDerived :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    (moduleDerivedPushforward f).IsRightDerivedFunctor (unit f)
      (HomologicalComplex.quasiIso (Modules X) (up ℤ)))

end moduleDerivedPushforward

end AlgebraicGeometry.AlgebraicSpace.Modules
