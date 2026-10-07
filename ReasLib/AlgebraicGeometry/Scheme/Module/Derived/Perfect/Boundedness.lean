module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Triangulated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.CategoryTheory.Pretriangulated.Homological.ShiftVanishing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- A coherent module on a smooth proper scheme over a field, placed in degree zero,
defines a perfect derived object. -/
noncomputable def Perfect.ofCoherent {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [Smooth f]
    (F : X.Modules) (hF : F.IsCoherent) :
    RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace) :=
  { obj := (DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F
    property := sorry }

/-- The underlying derived object of a coherent module's perfect realization is its
degree-zero single complex. -/
theorem Perfect.ofCoherent_obj {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [Smooth f]
    (F : X.Modules) (hF : F.IsCoherent) :
    (Perfect.ofCoherent f F hF).obj =
      (DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F := sorry

/-- The degree-zero derived realization of a coherent module on a smooth proper
scheme over a field is perfect. -/
theorem Perfect.ofCoherent_isPerfect {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [Smooth f]
    (F : X.Modules) (hF : F.IsCoherent) :
    RingedSpace.ModuleDerived.IsPerfect (Perfect.ofCoherent f F hF).obj := sorry

/-- A homological functor on perfect complexes of a smooth proper scheme over a field,
with bounded shifted support on each object, has a uniform positive symmetric
shift-vanishing bound on all coherent modules placed in degree zero. -/
theorem exists_shiftVanishingIn_coherent
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [Smooth f]
    {A : Type v} [Category.{w} A] [Abelian A]
    (H : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace) ⥤ A)
    [H.IsHomological] [H.ShiftSequence ℤ]
    (hH : ∀ K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace),
      H.shiftVanishingBounded K) :
    ∃ m : ℕ+, ∀ (F : X.Modules) (hF : F.IsCoherent),
      H.shiftVanishingIn (-(m : ℤ)) (m : ℤ) (Perfect.ofCoherent f F hF) := sorry

/-- A cohomological functor on perfect complexes of a smooth proper scheme over a field,
with bounded shifted support on each object, has a uniform positive symmetric
shift-vanishing bound on all coherent modules placed in degree zero, expressed
through the covariant functor `H.rightOp`. -/
theorem exists_shiftVanishingIn_coherent_cohomological
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [Smooth f]
    {A : Type v} [Category.{w} A] [Abelian A]
    (H : (RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))ᵒᵖ ⥤ A)
    [H.rightOp.IsHomological] [H.rightOp.ShiftSequence ℤ]
    (hH : ∀ K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace),
      H.rightOp.shiftVanishingBounded K) :
    ∃ m : ℕ+, ∀ (F : X.Modules) (hF : F.IsCoherent),
      H.rightOp.shiftVanishingIn (-(m : ℤ)) (m : ℤ)
        (Perfect.ofCoherent f F hF) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
