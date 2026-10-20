module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein.Locus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyNoetherianFibers

/-!
# Base change of Gorenstein loci
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Y' : Scheme.{u}}

/-- Gorensteinness at a point is preserved and reflected by arbitrary base change of a flat,
locally finite-type scheme morphism. -/
theorem gorensteinAt_iff_of_pullback_snd
    (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f] (g : Y' ⟶ Y)
    (x' : (pullback f g : Scheme)) :
    (pullback.snd f g).gorensteinAt x' ↔
      f.gorensteinAt ((pullback.fst f g) x') := sorry

/-- The Gorenstein locus of a flat, locally finite-type scheme morphism pulls back to the
inverse image of the original Gorenstein locus. -/
theorem gorensteinLocus_pullback_snd
    (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f] (g : Y' ⟶ Y) :
    (pullback.snd f g).gorensteinLocus =
      (pullback.fst f g) ⁻¹' f.gorensteinLocus := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom.gorensteinAt

/-- Gorensteinness at a point ascends through a locally finite-type base
change when the original morphism has locally Noetherian fibres. -/
theorem pullback_of_isPullback
    {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    (h_fibers : LocallyNoetherianFibers f) [LocallyOfFiniteType g]
    (x' : X') (hg : f.gorensteinAt (g' x')) :
    f'.gorensteinAt x' := sorry

/-- Gorensteinness at a point descends from a base change when the original
morphism is flat at the corresponding point. -/
theorem of_isPullback_of_flatAt
    {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    (h_fibers : LocallyNoetherianFibers f) [LocallyOfFiniteType g]
    (x' : X') (hflat : f.flatAt (g' x'))
    (hg : f'.gorensteinAt x') :
    f.gorensteinAt (g' x') := sorry

/-- Gorensteinness at a point descends from a base change when the base
morphism is flat at the image of that point. -/
theorem of_isPullback_of_flatAt_base
    {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    (h_fibers : LocallyNoetherianFibers f) [LocallyOfFiniteType g]
    (x' : X') (hflat : g.flatAt (f' x'))
    (hg : f'.gorensteinAt x') :
    f.gorensteinAt (g' x') := sorry

end AlgebraicGeometry.Scheme.Hom.gorensteinAt
