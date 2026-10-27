/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Kernel

/-!
# Exactness of strict transforms of algebraic-space modules

A quasicoherent short complex that remains short exact after every base change
remains short exact after strict transform along a blowup.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The strict-transform functor of module sheaves preserves zero morphisms. -/
theorem strictTransformFunctor_map_zero
    {S : Scheme.{u}} {B B' X : AlgebraicSpace S} (b : B' ⟶ B)
    (E : ClosedSubspace B') (f : X ⟶ B) {M N : X.Modules} :
    (strictTransformFunctor b E f).map (0 : M ⟶ N) = 0 := sorry

/-- The short complex obtained by applying strict transform to each object and
morphism of a short complex of module sheaves. -/
noncomputable def strictTransformShortComplex
    {S : Scheme.{u}} {B B' X : AlgebraicSpace S} (b : B' ⟶ B)
    (E : ClosedSubspace B') (f : X ⟶ B) (C : ShortComplex X.Modules) :
    ShortComplex (strictTransformAmbient b f).Modules where
  X₁ := (strictTransformFunctor b E f).obj C.X₁
  X₂ := (strictTransformFunctor b E f).obj C.X₂
  X₃ := (strictTransformFunctor b E f).obj C.X₃
  f := (strictTransformFunctor b E f).map C.f
  g := (strictTransformFunctor b E f).map C.g
  zero := ((strictTransformFunctor b E f).map_comp C.f C.g).symm.trans
    ((congrArg (fun k => (strictTransformFunctor b E f).map k) C.zero).trans
      (strictTransformFunctor_map_zero b E f))

/-- A short complex of quasi-coherent module sheaves that is short exact after every
base change remains short exact after strict transform along a blowup. -/
@[stacks 0869]
theorem strictTransform_shortExact_of_forall_pullback_shortExact
    {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z]
    (f : X ⟶ B) (C : ShortComplex X.Modules)
    [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] [C.X₃.IsQuasicoherent]
    (hbase :
      ∀ {T : AlgebraicSpace S} (t : T ⟶ B),
        (C.map (Modules.pullback (pullback.fst f t))).ShortExact) :
    (strictTransformShortComplex b (Z.inverseImageSubspace b) f C).ShortExact := sorry

end AlgebraicGeometry.AlgebraicSpace
