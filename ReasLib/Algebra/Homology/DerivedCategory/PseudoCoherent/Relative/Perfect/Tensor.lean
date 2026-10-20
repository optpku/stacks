/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Perfect

/-!
# Relative perfectness and derived tensor products

This leaf contains the two tensor consequences of relative perfectness.  The tensor-stability
statement needs no flatness hypothesis on the algebra; flatness enters only when an absolutely
perfect `A`-complex is viewed as perfect relative to the base ring `R`.

@stack 0DHU
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.DerivedCategory

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- Over a flat `R`-algebra, every perfect object of `D(A)` is perfect relative to `R`. -/
@[stacks 0DHU "perfect objects are relative-perfect over a flat base"]
theorem IsPerfect.isPerfectOver [Module.Flat R A]
    {K : DerivedCategory (ModuleCat A)} (hK : K.IsPerfect) :
    IsPerfectOver R K := sorry
/- Proof strategy: apply `isPerfectOver_iff`; a perfect object is pseudo-coherent, and a bounded
finite-projective representative restricts to a bounded termwise flat `R`-complex because `A` is
flat over `R`, giving finite Tor dimension. -/

/-- Tensoring a relative-perfect object on the left by a perfect object preserves relative
perfectness. -/
@[stacks 0DHU "tensor stability of relative perfectness"]
theorem IsPerfect.tensor_isPerfectOver
    {K M : DerivedCategory (ModuleCat A)} (hK : K.IsPerfect) (hM : IsPerfectOver R M) :
    IsPerfectOver R (DerivedTensor.Bifunctor.obj K M) := sorry
/- Proof strategy: split relative perfectness with `isPerfectOver_iff`; use tensor stability of
pseudo-coherence when one factor is perfect, and compute the perfect factor by a bounded
finite-projective model to preserve the finite Tor bound of `M` over `R`. -/

/-- Lemma 15.84.3 (1), Stacks `0DHU`: for a flat finitely presented map `R → A`, every perfect
object of `D(A)` is perfect relative to `R`. -/
@[stacks 0DHU "(1)"]
theorem IsPerfect.isPerfectOver_of_flat_of_finitePresentation
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    {K : DerivedCategory (ModuleCat A)} (hK : K.IsPerfect) :
    IsPerfectOver R K := sorry
/- Proof strategy: apply `hK.isPerfectOver`; finite presentation is retained only to match the
source hypotheses. -/

/-- Lemma 15.84.3 (2), Stacks `0DHU`: for a flat finitely presented map `R → A`, tensoring an
`R`-perfect object on the left by a perfect `A`-complex preserves relative perfectness. -/
@[stacks 0DHU "(2)"]
theorem IsPerfect.tensor_isPerfectOver_of_flat_of_finitePresentation
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    {K M : DerivedCategory (ModuleCat A)} (hK : K.IsPerfect) (hM : IsPerfectOver R M) :
    IsPerfectOver R (DerivedTensor.Bifunctor.obj K M) := sorry
/- Proof strategy: apply `hK.tensor_isPerfectOver hM`; the finite-presentation instance is part of
the source specialization but is not needed by the reusable tensor theorem. -/

/-- The fixed-right derived tensor model also preserves relative perfectness
when its variable left factor is perfect. -/
@[stacks 0DHU "fixed-right tensor stability of relative perfectness"]
theorem IsPerfect.fixedRightTensor_isPerfectOver
    {K M : DerivedCategory (ModuleCat A)} (hK : K.IsPerfect) (hM : IsPerfectOver R M) :
    IsPerfectOver R (DerivedTensor.Right.obj K M) := sorry
/- Proof strategy: transport `hK.tensor_isPerfectOver hM` across the canonical comparison between
`DerivedTensor.Right.obj K M` and `DerivedTensor.Bifunctor.obj K M`, then use
`IsPerfectOver.ofIso`. -/

end CategoryTheory.DerivedCategory

end
