module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FiniteOrder
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree

/-!
# Morphism properties in finite-order deformations of algebraic spaces

This file records invariance of morphism properties of algebraic spaces in
cartesian diagrams of thickenings over a finite-order thickening of the base,
assuming the ambient source is flat over the thickened base.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry (Scheme)
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening

variable {S : Scheme.{u}} {X X' Y Y' B B' : AlgebraicSpace S}
variable {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'}
variable {f : X ⟶ Y} {f' : X' ⟶ Y'}
variable {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
variable [thickeningX : IsThickening iX] [thickeningY : IsThickening iY]
variable [finiteOrderB : IsFiniteOrderThickening iB] [flatX' : Flat pX']
variable (sq : CommSq f iX iY f')
variable (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
variable (pullbackX : IsPullback pX iX iB pX') (pullbackY : IsPullback pY iY iB pY')

include thickeningX thickeningY finiteOrderB flatX'
include sq triangle triangle' pullbackX pullbackY

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, with the ambient source flat over the thickened base,
the closed-fiber morphism is flat if and only if the
ambient morphism is flat. -/
theorem flat_iff : Flat f ↔ Flat f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, with the ambient source flat over the thickened base,
the closed-fiber morphism is an isomorphism if and only
if the ambient morphism is an isomorphism. -/
theorem isIso_iff : IsIso f ↔ IsIso f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, with the ambient source flat over the thickened base,
the closed-fiber morphism is an open immersion if and
only if the ambient morphism is an open immersion. -/
theorem isOpenImmersion_iff : IsOpenImmersion f ↔ IsOpenImmersion f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, with the ambient source flat over the thickened base,
the closed-fiber morphism is locally of finite
presentation if and only if the ambient morphism is locally of finite
presentation. -/
theorem locallyOfFinitePresentation_iff :
    LocallyOfFinitePresentation f ↔ LocallyOfFinitePresentation f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, with the ambient source flat over the thickened base,
the closed-fiber morphism is syntomic if and only if the
ambient morphism is syntomic. -/
theorem syntomic_iff : Syntomic f ↔ Syntomic f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, with the ambient source flat over the thickened base,
the closed-fiber morphism is smooth if and only if the
ambient morphism is smooth. -/
theorem smooth_iff : Smooth f ↔ Smooth f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, with the ambient source flat over the thickened base,
the closed-fiber morphism is étale if and only if the
ambient morphism is étale. -/
theorem etale_iff : Etale f ↔ Etale f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, with the ambient source flat over the thickened base,
the closed-fiber morphism is finite locally free if and
only if the ambient morphism is finite locally free. -/
theorem finiteLocallyFree_iff : FiniteLocallyFree f ↔ FiniteLocallyFree f' := sorry

/-- In a cartesian diagram of thickenings of algebraic spaces over a finite-order
thickening of the base, with the ambient source flat over the thickened base,
the closed-fiber morphism is finite locally free of rank
`d` if and only if the ambient morphism is finite locally free of rank `d`. -/
theorem finiteLocallyFreeOfRank_iff (d : ℕ) :
    FiniteLocallyFreeOfRank f d ↔ FiniteLocallyFreeOfRank f' d := sorry

end AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening
