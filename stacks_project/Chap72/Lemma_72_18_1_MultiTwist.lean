/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.TensorPower.Multi

/-!
# Finite families of tensor twists on algebraic spaces

Typed checks expose the ordered tensor twist construction, its defining equation,
and preservation of coherence.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.TensorPower

#check (AlgebraicGeometry.AlgebraicSpace.Modules.TensorPower.multiTwist :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) {r : ℕ}
    (L : Fin r → X.Modules) [∀ j : Fin r, isInvertibleObject (L j)]
    (n : Fin r → ℤ), X.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.TensorPower.multiTwist_def :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) {r : ℕ}
    (L : Fin r → X.Modules) [∀ j : Fin r, isInvertibleObject (L j)]
    (n : Fin r → ℤ),
    multiTwist F L n =
      (List.finRange r).foldl
        (fun acc j ↦ tensorObj acc (InvertiblePower.obj (L j) (n j))) F)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.TensorPower.instIsCoherent_multiTwist :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] {r : ℕ} (L : Fin r → X.Modules)
    [∀ j : Fin r, isInvertibleObject (L j)] (n : Fin r → ℤ),
    (multiTwist F L n).IsCoherent)

end AlgebraicGeometry.AlgebraicSpace.Modules.TensorPower
