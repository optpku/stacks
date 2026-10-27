/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Relative.FiberSpecialization
import StacksCheckRecall

/-!
# Lemma 77.6.1

On a decent algebraic space locally of finite type over a scheme, a relatively
associated point of a finite-type quasi-coherent module that specializes into a
fibre along which the module is flat specializes to a relatively associated
point of that fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace TopologicalSpace

universe u

open AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 77.6.1: Let `S` be a scheme. Let `X` be a decent algebraic space
locally of finite type over `S`. Let `ℱ` be a finite type, quasi-coherent
`𝒪_X`-module. Let `s ∈ S` such that `ℱ` is flat over `S` at all points of
`|X_s|`. Let `x' ∈ Ass_{X/S}(ℱ)`. If the closure of `{x'}` in `|X|` meets
`|X_s|`, then the closure meets `Ass_{X/S}(ℱ) ∩ |X_s|`.
Here `Ass_{X/S}(ℱ)` is `relativeAssassin (SchemeRealization.toBase X) ℱ` and `|X_s|` is
`Points.base ⁻¹' {s}`. -/
@[stacks 0CW1]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.relativeAssassin.exists_mem_fiber_of_specializes :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] [LocallyOfFiniteType (SchemeRealization.toBase X)] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (s : S) {x' : Points X}
    (hx' : x' ∈ relativeAssassin (SchemeRealization.toBase X) ℱ)
    (hflat : ∀ z : Points X, Points.base z = s →
      flatOverAt ℱ (SchemeRealization.toBase X) z)
    (hmeets : ∃ t : Points X, Points.base t = s ∧ Specializes x' t),
    ∃ x : Points X,
      Points.base x = s ∧ x ∈ relativeAssassin (SchemeRealization.toBase X) ℱ ∧
        Specializes x' x)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.relativeAssassin.exists_mem_fiber_of_closure_meets :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] [LocallyOfFiniteType (SchemeRealization.toBase X)] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (s : S) {x' : Points X}
    (hx' : x' ∈ relativeAssassin (SchemeRealization.toBase X) ℱ)
    (hflat : ∀ z : Points X, Points.base z = s →
      flatOverAt ℱ (SchemeRealization.toBase X) z)
    (hmeets : (closure {x'} ∩ Points.base ⁻¹' {s}).Nonempty),
    (closure {x'} ∩ relativeAssassin (SchemeRealization.toBase X) ℱ ∩
      Points.base ⁻¹' {s}).Nonempty)
