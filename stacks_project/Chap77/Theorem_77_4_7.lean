/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.AssociatedPoints
import StacksCheckRecall

/-!
# Checking relative flatness at associated points of a fibre

For a locally finite-type morphism of algebraic spaces and a finite-type quasicoherent
module, relative flatness at a point follows from relative flatness at the relatively
weakly associated points of the set-theoretic fibre that specialize to it. The converse
holds when the source and target are decent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Theorem 77.4.7: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` which is locally of finite type. Let `ℱ` be a quasi-coherent `𝒪_X`-module
of finite type. Let `x ∈ |X|` with image `y = Points.map f x ∈ |Y|`, and write
`F = Points.map f ⁻¹' {y} ⊂ |X|` for the set-theoretic fibre. If `ℱ` is flat over `Y` at
every point of `F ∩ relativeWeakAss f ℱ` that specializes to `x`, then `ℱ` is flat at `x`
over `Y`. The converse holds when `X` and `Y` are decent. Under locally of finite type,
`Ass_{X/Y}(ℱ)` agrees with `relativeWeakAss f ℱ`. -/
@[stacks 0CWL]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverAt_of_relativeWeakAss_specializingTo :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (x : Points X)
    (h : ∀ x' ∈ relativeWeakAss f ℱ ∩ Points.map f ⁻¹' {Points.map f x},
      Specializes x' x → flatOverAt ℱ f x'),
    flatOverAt ℱ f x)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.relativeWeakAss_specializingTo_of_flatOverAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    {x x' : Points X} (hflat : flatOverAt ℱ f x)
    (hx'_ass_fiber : x' ∈ relativeWeakAss f ℱ ∩ Points.map f ⁻¹' {Points.map f x})
    (hspec : Specializes x' x),
    flatOverAt ℱ f x')

#check (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverAt_iff_relativeWeakAss_specializingTo :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (x : Points X),
    flatOverAt ℱ f x ↔
      ∀ x' ∈ relativeWeakAss f ℱ ∩ Points.map f ⁻¹' {Points.map f x},
        Specializes x' x → flatOverAt ℱ f x')
