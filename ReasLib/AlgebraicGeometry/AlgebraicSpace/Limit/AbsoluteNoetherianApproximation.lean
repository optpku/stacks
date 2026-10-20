/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Absolute Noetherian approximation of algebraic spaces

A quasi-compact quasi-separated algebraic space over `Spec ℤ` may be realized
as a directed inverse limit of quasi-separated algebraic spaces of finite type
over `ℤ` with affine transition morphisms.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A directed affine inverse system of quasi-separated finite-type algebraic
spaces over `ℤ`, together with a limit identification of a given algebraic
space with the cone vertex. -/
structure AbsoluteNoetherianApproximation (X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))) where
  /-- The directed index type of the approximating inverse system. -/
  I : Type u
  /-- The preorder on the index type of the approximating inverse system. -/
  [preorderI : Preorder I]
  /-- The approximating inverse system has at least one stage. -/
  [nonemptyI : Nonempty I]
  /-- Any two stages of the approximating inverse system admit a common later stage. -/
  [directedI : IsDirected I (· ≤ ·)]
  /-- The inverse system of approximating algebraic spaces over `Spec ℤ`. -/
  D : OrderDual I ⥤ AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))
  /-- A cone from the approximating inverse system. -/
  c : Cone D
  /-- The cone is a limit cone. -/
  isLimit : IsLimit c
  /-- The identification of `X` with the vertex of the limit cone. -/
  iso : X ≅ c.pt
  /-- Every transition morphism in the inverse system is affine. -/
  transitionAffine :
    ∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))
  /-- Every approximating stage is quasi-separated. -/
  stageQuasiSeparated :
    ∀ i : I, IsQuasiSeparated (D.obj (OrderDual.toDual i))
  /-- Every approximating stage is of finite type over `Spec ℤ`. -/
  stageFiniteType :
    ∀ i : I, FiniteType (SchemeRealization.toBase (D.obj (OrderDual.toDual i)))

namespace AbsoluteNoetherianApproximation

/-- Package a directed affine inverse system of quasi-separated finite-type
algebraic spaces over `ℤ`, together with a limit identification, as an absolute
Noetherian approximation. -/
def of (X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))) (c : Cone D)
    (isLimit : IsLimit c) (iso : X ≅ c.pt)
    (transitionAffine :
      ∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii')))
    (stageQuasiSeparated :
      ∀ i : I, IsQuasiSeparated (D.obj (OrderDual.toDual i)))
    (stageFiniteType :
      ∀ i : I, FiniteType (SchemeRealization.toBase (D.obj (OrderDual.toDual i)))) :
    AbsoluteNoetherianApproximation X where
  I := I
  D := D
  c := c
  isLimit := isLimit
  iso := iso
  transitionAffine := transitionAffine
  stageQuasiSeparated := stageQuasiSeparated
  stageFiniteType := stageFiniteType

end AbsoluteNoetherianApproximation

/-- A quasi-compact quasi-separated algebraic space over `Spec ℤ` admits a
directed affine inverse system of quasi-separated finite-type algebraic spaces
over `ℤ` whose limit is isomorphic to it. -/
theorem exists_absoluteNoetherianApproximation
    (X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))) [IsQuasiCompact X] [IsQuasiSeparated X] :
    Nonempty (AbsoluteNoetherianApproximation X) :=
  sorry

/-- Absolute Noetherian approximation of a qcqs algebraic space over `Spec ℤ` is
equivalent to the existence of a directed inverse system with affine transitions,
quasi-separated finite-type stages over `ℤ`, and a limit identification. -/
theorem exists_absoluteNoetherianApproximation_nonempty_iff
    (X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))) [IsQuasiCompact X] [IsQuasiSeparated X] :
    Nonempty (AbsoluteNoetherianApproximation X) ↔
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (D : OrderDual I ⥤ AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))) (c : Cone D)
        (_ : IsLimit c) (_ : X ≅ c.pt)
        (_ : ∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h)))
        (_ : ∀ i, IsQuasiSeparated (D.obj (OrderDual.toDual i))),
        ∀ i, FiniteType (SchemeRealization.toBase (D.obj (OrderDual.toDual i))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
