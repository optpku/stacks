/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.RingTheory.Flat.LocalAlgebra.Flattening.Corepresentability

/-!
# Local flattening loci

This module gives closed flattening loci over affine henselian local bases.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Flattening

/-- Over an affine henselian local base, the condition that a finite-type quasicoherent
module is flat at the points of a pointed fibre mapping to a fixed point is represented by
a closed subscheme. -/
theorem exists_closedImmersion_at {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
    [IsAffine S] [HenselianLocalRing Γ(S, ⊤)] [LocallyOfFiniteType f]
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (x : X) (s : S) (hx : f x = s)
    (hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤)) :
    ∃ Z : Over S, IsClosedImmersion Z.hom ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S) (t : T), g t = s →
        ((∀ y : (pullback.snd f g).fiber t,
            pullback.fst f g ((pullback.snd f g).fiberι t y) = x →
              flatOverAt (Scheme.Modules.baseChangeModule f g ℱ) (pullback.snd f g)
                ((pullback.snd f g).fiberι t y)) ↔
          Nonempty (Over.mk (T.fromSpecStalk t ≫ g) ⟶ Z)) := sorry

/-- If the morphism and the module stalk are finitely presented at the chosen point, the
closed flattening subscheme over an affine henselian local base can be chosen finitely
presented over that base. -/
theorem exists_closedImmersion_at_of_finitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
    [IsAffine S] [HenselianLocalRing Γ(S, ⊤)] [LocallyOfFiniteType f]
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (x : X) (s : S) (hx : f x = s)
    (hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤))
    (hf : f.FinitePresentationAt x)
    [Module.FinitePresentation (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)] :
    ∃ Z : Over S, IsClosedImmersion Z.hom ∧ Scheme.Hom.FinitePresentation Z.hom ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S) (t : T), g t = s →
        ((∀ y : (pullback.snd f g).fiber t,
            pullback.fst f g ((pullback.snd f g).fiberι t y) = x →
              flatOverAt (Scheme.Modules.baseChangeModule f g ℱ) (pullback.snd f g)
                ((pullback.snd f g).fiberι t y)) ↔
          Nonempty (Over.mk (T.fromSpecStalk t ≫ g) ⟶ Z)) := sorry

end AlgebraicGeometry.Scheme.Modules.Flattening
