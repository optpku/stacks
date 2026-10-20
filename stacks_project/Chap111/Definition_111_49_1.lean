/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Cartier.Weil
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Weil
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Principal
public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Stalk
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.IdealSheafData
open AlgebraicGeometry.LocallyRingedSpace
open CategoryTheory Opposite TopCat.Presheaf

universe u

/- Definition 111.49.1 (1): a Weil divisor on a Noetherian integral scheme `X` is a formal
integer linear combination of prime divisors. This is the owner `WeilDivisor`. -/
@[stacks 02AR]
#check (AlgebraicGeometry.WeilDivisor : Scheme.{u} → Type u)

/- Definition 111.49.1 (2): a prime divisor on `X` is an integral closed subscheme `Z ⊆ X`
whose generic point `ξ` has `ringKrullDim (𝒪_{X, ξ}) = 1`. This is the owner `PrimeDivisor`. -/
@[stacks 02AR]
#check (AlgebraicGeometry.PrimeDivisor : Scheme.{u} → Type u)

/- Definition 111.49.1 (3): the Weil divisor associated to a rational function `f ∈ K(X)ˣ`
is `∑ v_Z(f) [Z]`, where `v_Z` is the order of vanishing along the prime divisor `Z`.
This is the owner `principalWeilDivisor`. -/
@[stacks 02AR]
#check (AlgebraicGeometry.Scheme.principalWeilDivisor :
  (X : Scheme.{u}) → [IsLocallyNoetherian X] → [IsIntegral X] →
    X.functionFieldˣ → WeilDivisor X)

/- Definition 111.49.1 (4): an effective Cartier divisor on a scheme `S` is a closed subscheme
which is locally cut out by a nonzerodivisor on affine opens. The mathlib-style owner is
`IsEffectiveCartierDivisor`; the affine-local generator form is
`AffineLocalNonZeroDivisorGenerator`. -/
@[stacks 02AR]
#check (AlgebraicGeometry.IsEffectiveCartierDivisor :
  {S D : Scheme.{u}} → (D ⟶ S) → Prop)

/- Definition 111.49.1 (5): the Weil divisor associated to an effective Cartier divisor `D ⊆ X`
is `∑ v_Z(D) [Z]`, with `v_Z(D)` the length-order of a local nonzerodivisor equation along each
prime divisor. -/
@[stacks 02AR]
#check (AlgebraicGeometry.Scheme.weilDivisor_ofEffectiveCartier :
  {X : Scheme.{u}} → [IsNoetherian X] → [IsIntegral X] →
    (D : X.IdealSheafData) → [IsEffectiveCartierDivisor D.subschemeι] → WeilDivisor X)

/- Definition 111.49.1 (6): the sheaf of total quotient rings `𝒦_S` is the sheafification of the
presheaf sending `U` to the localization of `𝒪_S(U)` at sections whose germs are nonzerodivisors.
This is the owner `meromorphicFunctionSheaf`. -/
@[stacks 02AR]
#check (AlgebraicGeometry.LocallyRingedSpace.meromorphicFunctionSheaf :
  (S : LocallyRingedSpace.{u}) → TopCat.Sheaf CommRingCat.{u} S.toTopCat)

/- Definition 111.49.1 (7): a Cartier divisor on a scheme `S` is a global section of the quotient
sheaf `𝒦_S^⁎ / 𝒪_S^⁎`. This is the owner `CartierDivisor`. -/
@[stacks 02AR]
#check (AlgebraicGeometry.Scheme.CartierDivisor :
  (S : Scheme.{u}) →
    [HasSheafify (Opens.grothendieckTopology S.toTopCat) AddCommGrpCat.{u}] →
    [(Opens.grothendieckTopology S.toTopCat).HasSheafCompose
      (CategoryTheory.forget CommRingCat.{u})] → Type u)

/- Definition 111.49.1 (8): the Weil divisor associated to a Cartier divisor
`τ ∈ Γ(X, 𝒦_X^⁎ / 𝒪_X^⁎)` is `∑ v_Z(τ) [Z]`, with `v_Z(τ)` the length-order of a local
meromorphic representative `a / b` along each prime divisor. -/
@[stacks 02AR]
#check (AlgebraicGeometry.Scheme.weilDivisor_ofCartier :
  {X : Scheme.{u}} → [IsNoetherian X] → [IsIntegral X] →
    [HasSheafify (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}] →
    [(Opens.grothendieckTopology X.toTopCat).HasSheafCompose
      (CategoryTheory.forget CommRingCat.{u})] → CartierDivisor X → WeilDivisor X)
