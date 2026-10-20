/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension

/-!
# Closed subschemes in limits of schemes

This file records approximation results for closed subschemes under changes of base.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit.ClosedSubscheme

/-- A closed subscheme over a quasi-compact base change that avoids one fiber descends,
after restricting to an affine neighborhood of the point, to a closed subscheme over an affine
scheme locally of finite presentation over the original base, while continuing to avoid the
corresponding fiber. -/
theorem existsAffineApproximationAvoidingFiber
    {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] (g : T ⟶ S)
    (t : T) (Z : (pullback f g).IdealSheafData)
    (hZt : Scheme.IdealSheafData.avoidsFiber (pullback.snd f g) Z t) :
    ∃ (V : T.Opens) (hVt : t ∈ (V : Set T)) (_ : IsAffine V.toScheme)
      (T' : Scheme.{u}) (b : T' ⟶ S) (_ : LocallyOfFinitePresentation b)
      (_ : IsAffine T') (a : V.toScheme ⟶ T') (_ : CommSq a V.ι b g)
      (Z' : (pullback f b).IdealSheafData)
      (_ : Scheme.IdealSheafData.avoidsFiber (pullback.snd f b) Z' (a ⟨t, hVt⟩))
      (toXT : pullback f (V.ι ≫ g) ⟶ pullback f g)
      (toXT' : pullback f (V.ι ≫ g) ⟶ pullback f b)
      (_ : toXT ≫ pullback.fst f g = pullback.fst f (V.ι ≫ g))
      (_ : toXT ≫ pullback.snd f g = pullback.snd f (V.ι ≫ g) ≫ V.ι)
      (_ : toXT' ≫ pullback.fst f b = pullback.fst f (V.ι ≫ g))
      (_ : toXT' ≫ pullback.snd f b = pullback.snd f (V.ι ≫ g) ≫ a),
      Z'.comap toXT' ≤ Z.comap toXT := sorry

/-- A closed immersion into a quasi-compact and quasi-separated scheme is the limit, over the
target, of a nonempty directed inverse system of closed immersions of finite presentation. -/
theorem existsFinitePresentationLimit
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    [CompactSpace Y] [QuasiSeparatedSpace Y] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : OrderDual I ⥤ Over Y)
      (π : (Functor.const (OrderDual I)).obj (Over.mk i) ⟶ D),
      Nonempty (IsLimit (⟨Over.mk i, π⟩ : Cone D)) ∧
        ∀ j : I,
          IsClosedImmersion (D.obj j).hom ∧
            Scheme.Hom.FinitePresentation (D.obj j).hom := sorry

/-- A closed subscheme with fiber dimension at most `d` inside a finitely presented scheme over
a quasi-compact and quasi-separated base is contained in a closed subscheme of finite presentation
whose fibers still have dimension at most `d`. -/
theorem existsFinitePresentationContainingOfFiberDimensionLE
    {X S : Scheme.{u}} [CompactSpace S.carrier] [QuasiSeparatedSpace S.carrier]
    (f : X ⟶ S) [Scheme.Hom.FinitePresentation f] (d : ℕ) (Z : X.IdealSheafData)
    (hZdim : ∀ z : Z.subscheme, (Z.subschemeι ≫ f).fiberDimensionAt z ≤ (d : WithBot ℕ∞)) :
    ∃ Z' : X.IdealSheafData,
      ∃ _ : Z' ≤ Z, Scheme.Hom.FinitePresentation Z'.subschemeι ∧
        ∀ z : Z'.subscheme,
          (Z'.subschemeι ≫ f).fiberDimensionAt z ≤ (d : WithBot ℕ∞) := sorry

end AlgebraicGeometry.Scheme.Limit.ClosedSubscheme
