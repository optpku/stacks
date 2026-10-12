/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberIntegral

/-!
# Weightings of locally quasi-finite morphisms

This module defines integer-valued weightings using fibre integrals after
étale base change and restriction to a finite open subscheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An integer-valued function on the source of a locally quasi-finite morphism is a
weighting if its fibre integral is locally constant on every finite open restriction
after étale base change. -/
def IsWeighting {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    (w : X → ℤ) : Prop :=
  ∀ {V : Scheme.{u}} (g : V ⟶ Y) [Etale g] (U : (pullback f g).Opens)
      [IsFinite (U.ι ≫ pullback.snd f g)],
    IsLocallyConstant
      ((U.ι ≫ pullback.snd f g).fiberIntegral
        ⟨(U.ι ≫ pullback.snd f g).tendsto_cofinite_cofinite⟩
        (fun u : U ↦ w ((U.ι ≫ pullback.fst f g) u)))

/-- A function is a weighting exactly when all its finite étale-base-change fibre
integrals are locally constant. -/
theorem isWeighting_iff {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    (w : X → ℤ) :
    f.IsWeighting w ↔
      ∀ {V : Scheme.{u}} (g : V ⟶ Y) [Etale g] (U : (pullback f g).Opens)
          [IsFinite (U.ι ≫ pullback.snd f g)],
        IsLocallyConstant
          ((U.ι ≫ pullback.snd f g).fiberIntegral
            ⟨(U.ι ≫ pullback.snd f g).tendsto_cofinite_cofinite⟩
            (fun u : U ↦ w ((U.ι ≫ pullback.fst f g) u))) := sorry

/-- A weighting gives a locally constant fibre integral on any chosen finite open
restriction after étale base change. -/
theorem IsWeighting.locallyConstant {X Y : Scheme.{u}} {f : X ⟶ Y}
    [LocallyQuasiFinite f] {w : X → ℤ} (hw : f.IsWeighting w)
    {V : Scheme.{u}} (g : V ⟶ Y) [Etale g] (U : (pullback f g).Opens)
    [IsFinite (U.ι ≫ pullback.snd f g)] :
    IsLocallyConstant
      ((U.ι ≫ pullback.snd f g).fiberIntegral
        ⟨(U.ι ≫ pullback.snd f g).tendsto_cofinite_cofinite⟩
        (fun u : U ↦ w ((U.ι ≫ pullback.fst f g) u))) := sorry

/-- The zero function is a weighting of every locally quasi-finite morphism. -/
theorem IsWeighting.zero {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] :
    f.IsWeighting (fun _ ↦ 0) := sorry

/-- Restricting a weighting of a locally quasi-finite morphism to an open subscheme
of its source again gives a weighting. -/
theorem IsWeighting.restrict {X Y : Scheme.{u}} {f : X ⟶ Y} [LocallyQuasiFinite f]
    {w : X → ℤ} (hw : f.IsWeighting w) (U : X.Opens) :
    (U.ι ≫ f).IsWeighting (fun x : U ↦ w x) := sorry

/-- The pointwise product of weightings of two composable locally quasi-finite
morphisms is a weighting of their composite. -/
theorem IsWeighting.comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [LocallyQuasiFinite f] [LocallyQuasiFinite g] {w_f : X → ℤ} {w_g : Y → ℤ}
    (hw_f : f.IsWeighting w_f) (hw_g : g.IsWeighting w_g) :
    (f ≫ g).IsWeighting (fun x ↦ w_f x * w_g (f x)) := sorry

end AlgebraicGeometry.Scheme.Hom
