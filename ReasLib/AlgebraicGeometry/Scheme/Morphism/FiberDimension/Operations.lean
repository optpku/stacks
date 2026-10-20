/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Composition.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension

/-!
# Operations on local fibre dimension

This leaf records composition and base-change formulas for
`Scheme.Hom.fiberDimensionAt`.  The local fibre-dimension definition itself
remains in the parent leaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Local fibre dimensions are subadditive under composition of locally
finite-type scheme morphisms. -/
theorem fiberDimensionAt_comp_le {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFiniteType f] [LocallyOfFiniteType g] (x : X) :
    (f ≫ g).fiberDimensionAt x ≤ f.fiberDimensionAt x + g.fiberDimensionAt (f x) := sorry

/-- Local fibre dimensions add under composition when the induced map from the
composite fibre to the intermediate fibre is flat at the selected point. -/
theorem fiberDimensionAt_comp_eq_add_of_flatAt_compFiberToBaseFiber {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFiniteType f] [LocallyOfFiniteType g] (x : X)
    (hflat : flatAt (compFiberToBaseFiber f g (g (f x))) (asFiber (f ≫ g) x)) :
    (f ≫ g).fiberDimensionAt x = f.fiberDimensionAt x + g.fiberDimensionAt (f x) := sorry

/-- Local fibre dimensions add under composition when the first morphism is
flat at the selected source point. -/
theorem fiberDimensionAt_comp_eq_add_of_flatAt {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFiniteType f] [LocallyOfFiniteType g] (x : X)
    (hflat : flatAt f x) :
    (f ≫ g).fiberDimensionAt x = f.fiberDimensionAt x + g.fiberDimensionAt (f x) := sorry

/-- Local fibre dimension is preserved by an arbitrary pullback square. -/
@[stacks 02FY "(1)"]
theorem fiberDimensionAt_eq_of_isPullback {S X S' X' : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (hpb : IsPullback g' f' f g) (x' : X') :
    f'.fiberDimensionAt x' = f.fiberDimensionAt (g' x') := sorry

/-- The canonical pullback projection preserves local fibre dimension. -/
theorem fiberDimensionAt_eq_of_pullback_snd {S X S' : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S)
    (x' : (pullback f g : Scheme)) :
    (pullback.snd f g).fiberDimensionAt x' =
      f.fiberDimensionAt (pullback.fst f g x') := sorry

/-- The topological-fibre spelling of the canonical pullback invariance
formula. -/
theorem topologicalKrullDimAt_asFiber_eq_of_pullback_snd {S X S' : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S)
    (x' : (pullback f g : Scheme)) :
    topologicalKrullDimAt ((pullback.snd f g).asFiber x') =
      topologicalKrullDimAt (f.asFiber (pullback.fst f g x')) := sorry

end AlgebraicGeometry.Scheme.Hom
