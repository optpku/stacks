/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReasLib.AlgebraicGeometry.Morphisms.Thickening
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Differentials

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Thickening.Hom

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient maps are
simultaneously closed immersions. -/
theorem isClosedImmersion_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom] :
    IsClosedImmersion g.left ↔ IsClosedImmersion g.right := sorry

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient maps are
simultaneously locally of finite type. -/
theorem locallyOfFiniteType_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom] :
    LocallyOfFiniteType g.left ↔ LocallyOfFiniteType g.right := sorry

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient maps are
simultaneously locally quasi-finite. -/
theorem locallyQuasiFinite_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom] :
    LocallyQuasiFinite g.left ↔ LocallyQuasiFinite g.right := sorry

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient maps have
relative dimension `d` simultaneously. -/
theorem relativeDimension_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom]
    (d : ℕ) :
    Scheme.Hom.RelativeDimension g.left d ↔ Scheme.Hom.RelativeDimension g.right d := sorry

/-- In a cartesian morphism to a finite-order thickening, the relative differential sheaves of
the closed and ambient maps vanish simultaneously. -/
theorem isZero_relativeDifferentials_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom] :
    IsZero (Ω[g.left.toShHom]) ↔ IsZero (Ω[g.right.toShHom]) := sorry

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient maps are
simultaneously unramified. -/
theorem unramified_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom] :
    Unramified g.left ↔ Unramified g.right := sorry

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient maps are
simultaneously proper. -/
theorem isProper_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom] :
    IsProper g.left ↔ IsProper g.right := sorry

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient maps are
simultaneously finite. -/
theorem isFinite_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom] :
    IsFinite g.left ↔ IsFinite g.right := sorry

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient maps are
simultaneously monomorphisms. -/
theorem mono_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom] :
    Mono g.left ↔ Mono g.right := sorry

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient maps are
simultaneously immersions. -/
theorem isImmersion_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom] :
    IsImmersion g.left ↔ IsImmersion g.right := sorry

end AlgebraicGeometry.Thickening.Hom
