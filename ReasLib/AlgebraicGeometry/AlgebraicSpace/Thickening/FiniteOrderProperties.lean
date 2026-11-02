/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Arrow
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FiniteOrder
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.CartesianProperties
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.FiniteType

/-!
# Cartesian transfer along finite-order thickenings of algebraic spaces

If a morphism of thickenings of algebraic spaces is cartesian and the source
thickening has finite order, then the listed morphism properties hold for the
closed map if and only if they hold for the ambient map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Thickening.Hom

/-- In a cartesian morphism from a finite-order thickening, the closed and ambient
maps are simultaneously locally of finite type. -/
theorem locallyOfFiniteType_iff_of_isPullback {S : Scheme.{u}}
    {T U : Thickening S} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening T.hom] :
    LocallyOfFiniteType g.left ↔ LocallyOfFiniteType g.right := sorry

/-- In a cartesian morphism from a finite-order thickening, the closed and ambient
maps are simultaneously closed immersions. -/
theorem isClosedImmersion_iff_of_isPullback {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening T.hom] :
    IsClosedImmersion g.left ↔ IsClosedImmersion g.right := by
  by_cases hleft : LocallyOfFiniteType g.left
  · letI : LocallyOfFiniteType g.left := hleft
    letI : LocallyOfFiniteType g.right :=
      (locallyOfFiniteType_iff_of_isPullback g sq).mp hleft
    exact Thickening.Hom.isClosedImmersion_iff g sq.flip
  · have hright : ¬ LocallyOfFiniteType g.right := by
      intro hright
      exact hleft ((locallyOfFiniteType_iff_of_isPullback g sq).mpr hright)
    constructor
    · intro h
      letI : IsClosedImmersion g.left := h
      exact (hleft (inferInstance : LocallyOfFiniteType g.left)).elim
    · intro h
      letI : IsClosedImmersion g.right := h
      exact (hright (inferInstance : LocallyOfFiniteType g.right)).elim

/-- In a cartesian morphism from a finite-order thickening, the closed and ambient
maps are simultaneously locally quasi-finite. -/
theorem locallyQuasiFinite_iff_of_isPullback {S : Scheme.{u}}
    {T U : Thickening S} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening T.hom] :
    LocallyQuasiFinite g.left ↔ LocallyQuasiFinite g.right := by
  by_cases hleft : LocallyOfFiniteType g.left
  · letI : LocallyOfFiniteType g.left := hleft
    letI : LocallyOfFiniteType g.right :=
      (locallyOfFiniteType_iff_of_isPullback g sq).mp hleft
    exact Thickening.Hom.locallyQuasiFinite_iff g sq.flip
  · have hright : ¬ LocallyOfFiniteType g.right := by
      intro hright
      exact hleft ((locallyOfFiniteType_iff_of_isPullback g sq).mpr hright)
    constructor
    · intro h
      letI : LocallyQuasiFinite g.left := h
      exact (hleft (inferInstance : LocallyOfFiniteType g.left)).elim
    · intro h
      letI : LocallyQuasiFinite g.right := h
      exact (hright (inferInstance : LocallyOfFiniteType g.right)).elim

/-- In a cartesian morphism from a finite-order thickening, the closed and ambient
maps are simultaneously locally of finite type of relative dimension `d`. -/
theorem relativeDimension_iff_of_isPullback {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening T.hom] (d : ℕ) :
    LocallyOfFiniteType g.left ∧ RelativeDimension g.left d ↔
      LocallyOfFiniteType g.right ∧ RelativeDimension g.right d := sorry

/-- In a cartesian morphism from a finite-order thickening, the relative
differential sheaves of the closed and ambient maps vanish simultaneously. -/
theorem isZero_relativeDifferentials_iff_of_isPullback {S : Scheme.{u}}
    {T U : Thickening S} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening T.hom] :
    IsZero (Ω[g.left]) ↔ IsZero (Ω[g.right]) := sorry

/-- In a cartesian morphism from a finite-order thickening, the closed and ambient
maps are simultaneously unramified. -/
theorem unramified_iff_of_isPullback {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening T.hom] :
    Unramified g.left ↔ Unramified g.right := by
  by_cases hleft : LocallyOfFiniteType g.left
  · letI : LocallyOfFiniteType g.left := hleft
    letI : LocallyOfFiniteType g.right :=
      (locallyOfFiniteType_iff_of_isPullback g sq).mp hleft
    exact Thickening.Hom.unramified_iff g sq.flip
  · have hright : ¬ LocallyOfFiniteType g.right := by
      intro hright
      exact hleft ((locallyOfFiniteType_iff_of_isPullback g sq).mpr hright)
    constructor
    · intro h
      letI : Unramified g.left := h
      exact (hleft (inferInstance : LocallyOfFiniteType g.left)).elim
    · intro h
      letI : Unramified g.right := h
      exact (hright (inferInstance : LocallyOfFiniteType g.right)).elim

/-- In a cartesian morphism from a finite-order thickening, the closed and ambient
maps are simultaneously proper. -/
theorem proper_iff_of_isPullback {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening T.hom] :
    Proper g.left ↔ Proper g.right := by
  by_cases hleft : LocallyOfFiniteType g.left
  · letI : LocallyOfFiniteType g.left := hleft
    letI : LocallyOfFiniteType g.right :=
      (locallyOfFiniteType_iff_of_isPullback g sq).mp hleft
    exact Thickening.Hom.proper_iff g sq.flip
  · have hright : ¬ LocallyOfFiniteType g.right := by
      intro hright
      exact hleft ((locallyOfFiniteType_iff_of_isPullback g sq).mpr hright)
    constructor
    · intro h
      letI : Proper g.left := h
      exact (hleft (inferInstance : LocallyOfFiniteType g.left)).elim
    · intro h
      letI : Proper g.right := h
      exact (hright (inferInstance : LocallyOfFiniteType g.right)).elim

/-- In a cartesian morphism from a finite-order thickening, the closed and ambient
maps are simultaneously finite. -/
theorem isFinite_iff_of_isPullback {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening T.hom] :
    IsFinite g.left ↔ IsFinite g.right := by
  by_cases hleft : LocallyOfFiniteType g.left
  · letI : LocallyOfFiniteType g.left := hleft
    letI : LocallyOfFiniteType g.right :=
      (locallyOfFiniteType_iff_of_isPullback g sq).mp hleft
    exact Thickening.Hom.isFinite_iff g sq.flip
  · have hright : ¬ LocallyOfFiniteType g.right := by
      intro hright
      exact hleft ((locallyOfFiniteType_iff_of_isPullback g sq).mpr hright)
    constructor
    · intro h
      letI : IsFinite g.left := h
      letI : Proper g.left := inferInstance
      exact (hleft (inferInstance : LocallyOfFiniteType g.left)).elim
    · intro h
      letI : IsFinite g.right := h
      letI : Proper g.right := inferInstance
      exact (hright (inferInstance : LocallyOfFiniteType g.right)).elim

/-- In a cartesian morphism from a finite-order thickening, the closed and ambient
maps are simultaneously monomorphisms. -/
theorem mono_iff_of_isPullback {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening T.hom] :
    Mono g.left ↔ Mono g.right := sorry

/-- In a cartesian morphism from a finite-order thickening, the closed and ambient
maps are simultaneously immersions. -/
theorem isImmersion_iff_of_isPullback {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening T.hom] :
    IsImmersion g.left ↔ IsImmersion g.right := by
  by_cases hleft : LocallyOfFiniteType g.left
  · letI : LocallyOfFiniteType g.left := hleft
    letI : LocallyOfFiniteType g.right :=
      (locallyOfFiniteType_iff_of_isPullback g sq).mp hleft
    exact Thickening.Hom.isImmersion_iff g sq.flip
  · have hright : ¬ LocallyOfFiniteType g.right := by
      intro hright
      exact hleft ((locallyOfFiniteType_iff_of_isPullback g sq).mpr hright)
    constructor
    · intro h
      letI : IsImmersion g.left := h
      exact (hleft (inferInstance : LocallyOfFiniteType g.left)).elim
    · intro h
      letI : IsImmersion g.right := h
      exact (hright (inferInstance : LocallyOfFiniteType g.right)).elim

end AlgebraicGeometry.AlgebraicSpace.Thickening.Hom
