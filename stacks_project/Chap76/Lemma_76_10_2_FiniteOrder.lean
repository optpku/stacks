/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import stacks_project.Chap76.Definition_76_7_2_Differentials
public import stacks_project.Chap76.Definition_76_9_1_Arrow
public import stacks_project.Chap76.Definition_76_9_1_FiniteOrder

/-!
# Cartesian transfer along finite-order thickenings of algebraic spaces

If a morphism of thickenings of algebraic spaces is cartesian and the target
thickening has finite order, then the listed morphism properties hold for the
closed map if and only if they hold for the ambient map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Thickening.Hom

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient
maps are simultaneously closed immersions. -/
theorem isClosedImmersion_iff_of_isPullback {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening U.hom] :
    IsClosedImmersion g.left ↔ IsClosedImmersion g.right := sorry

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient
maps are simultaneously locally of finite type. -/
theorem locallyOfFiniteType_iff_of_isPullback {S : Scheme.{u}}
    {T U : Thickening S} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening U.hom] :
    LocallyOfFiniteType g.left ↔ LocallyOfFiniteType g.right := sorry

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient
maps are simultaneously locally quasi-finite. -/
theorem locallyQuasiFinite_iff_of_isPullback {S : Scheme.{u}}
    {T U : Thickening S} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening U.hom] :
    LocallyQuasiFinite g.left ↔ LocallyQuasiFinite g.right := sorry

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient
maps are simultaneously locally of finite type of relative dimension `d`. -/
theorem relativeDimension_iff_of_isPullback {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening U.hom] (d : ℕ) :
    LocallyOfFiniteType g.left ∧ RelativeDimension g.left d ↔
      LocallyOfFiniteType g.right ∧ RelativeDimension g.right d := sorry

/-- In a cartesian morphism to a finite-order thickening, the relative
differential sheaves of the closed and ambient maps vanish simultaneously. -/
theorem isZero_relativeDifferentials_iff_of_isPullback {S : Scheme.{u}}
    {T U : Thickening S} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening U.hom] :
    IsZero (Ω[g.left]) ↔ IsZero (Ω[g.right]) := sorry

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient
maps are simultaneously unramified. -/
theorem unramified_iff_of_isPullback {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening U.hom] :
    Unramified g.left ↔ Unramified g.right := sorry

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient
maps are simultaneously proper. -/
theorem proper_iff_of_isPullback {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening U.hom] :
    Proper g.left ↔ Proper g.right := sorry

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient
maps are simultaneously finite. -/
theorem isFinite_iff_of_isPullback {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening U.hom] :
    IsFinite g.left ↔ IsFinite g.right := sorry

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient
maps are simultaneously monomorphisms. -/
theorem mono_iff_of_isPullback {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening U.hom] :
    Mono g.left ↔ Mono g.right := sorry

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient
maps are simultaneously immersions. -/
theorem isImmersion_iff_of_isPullback {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening U.hom] :
    IsImmersion g.left ↔ IsImmersion g.right := sorry

end AlgebraicGeometry.AlgebraicSpace.Thickening.Hom
