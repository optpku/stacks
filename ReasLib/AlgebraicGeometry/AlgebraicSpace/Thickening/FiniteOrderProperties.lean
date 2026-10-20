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
maps are simultaneously closed immersions. -/
theorem isClosedImmersion_iff_of_isPullback {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening T.hom] :
    IsClosedImmersion g.left ↔ IsClosedImmersion g.right := sorry

/-- In a cartesian morphism from a finite-order thickening, the closed and ambient
maps are simultaneously locally of finite type. -/
theorem locallyOfFiniteType_iff_of_isPullback {S : Scheme.{u}}
    {T U : Thickening S} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening T.hom] :
    LocallyOfFiniteType g.left ↔ LocallyOfFiniteType g.right := sorry

/-- In a cartesian morphism from a finite-order thickening, the closed and ambient
maps are simultaneously locally quasi-finite. -/
theorem locallyQuasiFinite_iff_of_isPullback {S : Scheme.{u}}
    {T U : Thickening S} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening T.hom] :
    LocallyQuasiFinite g.left ↔ LocallyQuasiFinite g.right := sorry

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
    Unramified g.left ↔ Unramified g.right := sorry

/-- In a cartesian morphism from a finite-order thickening, the closed and ambient
maps are simultaneously proper. -/
theorem proper_iff_of_isPullback {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening T.hom] :
    Proper g.left ↔ Proper g.right := sorry

/-- In a cartesian morphism from a finite-order thickening, the closed and ambient
maps are simultaneously finite. -/
theorem isFinite_iff_of_isPullback {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
    [IsFiniteOrderThickening T.hom] :
    IsFinite g.left ↔ IsFinite g.right := sorry

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
    IsImmersion g.left ↔ IsImmersion g.right := sorry

end AlgebraicGeometry.AlgebraicSpace.Thickening.Hom
