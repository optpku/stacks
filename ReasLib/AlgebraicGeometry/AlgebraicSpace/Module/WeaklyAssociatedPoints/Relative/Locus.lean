/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Relative

/-!
# Relative assassin of modules on algebraic spaces

When the fibres of `f : X ⟶ Y` are locally Noetherian, the relative assassin
`Ass_{X/Y}(F)` is the relative weak assassin of `F` in `X` over `Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The relative weak assassin of an `𝒪_X`-module `F` in `X` over `Y` is the
locus of points of `|X|` that arise from a weakly associated point of the
restriction of `F` to a field fibre representing `f(x)`. -/
def relativeWeakAss (f : X ⟶ Y) (F : X.Modules) : Set (Points X) :=
  {x | RelativeWeakAss.existsField f F x}

/-- A point of `|X|` lies in `relativeWeakAss f F` if and only if it is the
image of a weakly associated point of the restriction of `F` to a field fibre
representing `f(x)`. -/
theorem mem_relativeWeakAss_iff (f : X ⟶ Y) (F : X.Modules) (x : Points X) :
    x ∈ relativeWeakAss f F ↔
      ∃ (p : FieldValuedPoint Y) (t : Points (fieldFiber f p)),
        Points.mk p = Points.map f x ∧
          Points.map (fieldFiberι f p) t = x ∧
            t ∈ ((pullback (fieldFiberι f p)).obj F).weakAss :=
  Iff.rfl

/-- The relative assassin of an `𝒪_X`-module `F` in `X` over `Y`. Under locally
Noetherian fibres this is `Ass_{X/Y}(F)`, and it agrees with `relativeWeakAss`. -/
abbrev relativeAssassin (f : X ⟶ Y) (F : X.Modules) : Set (Points X) :=
  relativeWeakAss f F

/-- A point of `|X|` lies in `relativeAssassin f F` if and only if it is the
image of a weakly associated point of the restriction of `F` to a field fibre
representing `f(x)`. -/
theorem mem_relativeAssassin_iff (f : X ⟶ Y) (F : X.Modules) (x : Points X) :
    x ∈ relativeAssassin f F ↔
      ∃ (p : FieldValuedPoint Y) (t : Points (fieldFiber f p)),
        Points.mk p = Points.map f x ∧
          Points.map (fieldFiberι f p) t = x ∧
            t ∈ ((pullback (fieldFiberι f p)).obj F).weakAss :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
