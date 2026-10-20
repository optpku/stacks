/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.AbsoluteNoetherianApproximation

/-!
# Absolute Noetherian approximation of algebraic spaces

Compatibility names and typed checks for directed finite-type approximations
over the spectrum of the integers.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The spectrum of the universe-`u` lift of `ℤ`. -/
abbrev specULiftInt : Scheme.{u} :=
  Spec (CommRingCat.of (ULift.{u} ℤ))

/-- The structural morphism of an algebraic space to its base scheme. -/
abbrev toBase {S : Scheme.{u}} (X : AlgebraicSpace S) : X ⟶ ofOver (Over.mk (𝟙 S)) :=
  SchemeRealization.toBase X

#check (AlgebraicGeometry.AlgebraicSpace.AbsoluteNoetherianApproximation :
  AlgebraicSpace specULiftInt → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.AbsoluteNoetherianApproximation.of :
  ∀ (X : AlgebraicSpace specULiftInt)
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ AlgebraicSpace specULiftInt) (c : Cone D),
    IsLimit c → (X ≅ c.pt) →
      (∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))) →
      (∀ i : I, IsQuasiSeparated (D.obj (OrderDual.toDual i))) →
      (∀ i : I, FiniteType (toBase (D.obj (OrderDual.toDual i)))) →
      AbsoluteNoetherianApproximation X)

#check (AlgebraicGeometry.AlgebraicSpace.exists_absoluteNoetherianApproximation :
  ∀ (X : AlgebraicSpace specULiftInt) [IsQuasiCompact X] [IsQuasiSeparated X],
    Nonempty (AbsoluteNoetherianApproximation X))

#check (AlgebraicGeometry.AlgebraicSpace.exists_absoluteNoetherianApproximation_nonempty_iff :
  ∀ (X : AlgebraicSpace specULiftInt) [IsQuasiCompact X] [IsQuasiSeparated X],
    Nonempty (AbsoluteNoetherianApproximation X) ↔
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (D : OrderDual I ⥤ AlgebraicSpace specULiftInt) (c : Cone D)
        (_ : IsLimit c) (_ : X ≅ c.pt)
        (_ : ∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h)))
        (_ : ∀ i, IsQuasiSeparated (D.obj (OrderDual.toDual i))),
        ∀ i, FiniteType (toBase (D.obj (OrderDual.toDual i))))

end AlgebraicGeometry.AlgebraicSpace
