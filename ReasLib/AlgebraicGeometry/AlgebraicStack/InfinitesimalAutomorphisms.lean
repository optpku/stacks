module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation.BaseChange
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.StrongRimSchlessinger
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps

/-!
# Flat base change of infinitesimal automorphism modules

Infinitesimal automorphisms of an algebraic stack with locally finitely presented
inertia commute with flat extension of scalars.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- For an algebraic stack with locally finitely presented inertia, the canonical
comparison on infinitesimal automorphism modules along a flat algebra map is an
isomorphism. -/
theorem infExtendScalars_isIso {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X]
    [Groupoids.Hom.LocallyOfFinitePresentation (forget.{u + 1, u, u, u + 1} X)]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB) (hflat : v.hom.Flat)
    (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    IsIso (infExtendScalars v hv x M) :=
  sorry

/-- The canonical comparison on infinitesimal automorphism modules of an algebraic
stack with locally finitely presented inertia is invertible under flat scalar
extension. -/
instance infExtendScalars.instIsIso {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X]
    [Groupoids.Hom.LocallyOfFinitePresentation (forget.{u + 1, u, u, u + 1} X)]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB) [Fact v.hom.Flat]
    (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    IsIso (infExtendScalars v hv x M) :=
  infExtendScalars_isIso v hv Fact.out x M

end AlgebraicGeometry.GroupoidsOver
