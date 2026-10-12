/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import ReasLib.RingTheory.Depth.CohenMacaulay

@[expose] public section

/-!
# Depth in a finite-free presentation over a Cohen--Macaulay local ring

@stack 00NE

The middle term is described intrinsically by finite-free module instances;
choosing coordinates is proof-side data and is not part of the public API.
-/

open CategoryTheory

universe u v

namespace CategoryTheory.ShortComplex.ShortExact

/-- Lemma 10.104.8 (00NE): in a short exact sequence with finite-free middle
term over a `d`-dimensional Cohen--Macaulay local ring, either the cokernel is
zero, the kernel has greater depth, or both endpoint depths equal `d`. -/
@[stacks 00NE]
theorem moduleDepth_kernel_trichotomy_of_finiteFree
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Module.CohenMacaulay R R] {S : ShortComplex (ModuleCat.{v} R)}
    [Module.Free R S.X₂] [Module.Finite R S.X₂]
    {d : ℕ} (hdim : ringKrullDim R = d) (hS : S.ShortExact) :
    Subsingleton S.X₃ ∨ moduleDepth R S.X₁ > moduleDepth R S.X₃ ∨
      moduleDepth R S.X₁ = d ∧ moduleDepth R S.X₃ = d := sorry

end CategoryTheory.ShortComplex.ShortExact
