module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyUnramified.Differentials

/-!
# Unramified morphisms of algebraic spaces versus vanishing differentials

A morphism of algebraic spaces is unramified if and only if it is locally of
finite type and either its sheaf of relative differentials vanishes or it is
formally unramified.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces over a scheme is unramified if and only if
it is locally of finite type and its sheaf of relative differentials vanishes. -/
theorem unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Unramified f ↔ LocallyOfFiniteType f ∧ IsZero (Ω[f]) :=
  sorry

/-- A morphism of algebraic spaces over a scheme is unramified if and only if
it is locally of finite type and formally unramified. -/
theorem unramified_iff_locallyOfFiniteType_and_formallyUnramified
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Unramified f ↔ LocallyOfFiniteType f ∧ FormallyUnramified f := by
  constructor
  · intro h
    obtain ⟨hft, hzero⟩ :=
      (unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials f).mp h
    exact ⟨hft, (formallyUnramified_iff_isZero_relativeDifferentials f).mpr hzero⟩
  · rintro ⟨hft, hformal⟩
    exact (unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials f).mpr
      ⟨hft, (formallyUnramified_iff_isZero_relativeDifferentials f).mp hformal⟩

/-- An unramified morphism of algebraic spaces is formally unramified. -/
instance formallyUnramified_of_unramified {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Unramified f] : FormallyUnramified f :=
  ((unramified_iff_locallyOfFiniteType_and_formallyUnramified f).mp
    (inferInstance : Unramified f)).2

/-- A morphism of algebraic spaces that is locally of finite type and formally
unramified is unramified. -/
instance unramified_of_locallyOfFiniteType_of_formallyUnramified
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [FormallyUnramified f] : Unramified f :=
  (unramified_iff_locallyOfFiniteType_and_formallyUnramified f).mpr
    ⟨inferInstance, inferInstance⟩

/-- A morphism of algebraic spaces that is locally of finite type and whose
sheaf of relative differentials vanishes is unramified. -/
theorem unramified_of_locallyOfFiniteType_of_isZero_relativeDifferentials
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (h : IsZero (Ω[f])) : Unramified f :=
  (unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials f).mpr
    ⟨inferInstance, h⟩

namespace Unramified

/-- An algebraic-space morphism that is locally of finite type is unramified if
and only if its sheaf of relative differentials vanishes. -/
theorem iff_isZero_relativeDifferentials {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [LocallyOfFiniteType f] : Unramified f ↔ IsZero (Ω[f]) := by
  constructor
  · intro h
    exact ((unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials f).mp h).2
  · intro h
    exact (unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials f).mpr
      ⟨inferInstance, h⟩

/-- An algebraic-space morphism that is locally of finite type is unramified if
and only if it is formally unramified. -/
theorem iff_formallyUnramified {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [LocallyOfFiniteType f] :
    Unramified f ↔ FormallyUnramified f := by
  constructor
  · intro h
    exact ((unramified_iff_locallyOfFiniteType_and_formallyUnramified f).mp h).2
  · intro h
    exact (unramified_iff_locallyOfFiniteType_and_formallyUnramified f).mpr
      ⟨inferInstance, h⟩

end Unramified

end AlgebraicGeometry.AlgebraicSpace
