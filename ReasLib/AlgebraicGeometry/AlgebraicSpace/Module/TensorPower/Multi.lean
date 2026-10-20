module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.CategoryTheory.Monoidal.InvertiblePower

/-!
# Finite families of tensor twists on algebraic spaces

Integral powers of a finite family of invertible modules act on a module by an
ordered tensor product. On locally Noetherian algebraic spaces this preserves coherence.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.TensorPower

/-- The ordered tensor twist of a module by integral powers of a finite family of
invertible modules on an algebraic space. -/
noncomputable def multiTwist
    {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) {r : ℕ}
    (L : Fin r → X.Modules) [∀ j : Fin r, isInvertibleObject (L j)]
    (n : Fin r → ℤ) : X.Modules :=
  (List.finRange r).foldl
    (fun acc j ↦ tensorObj acc (InvertiblePower.obj (L j) (n j))) F

/-- The ordered fold expression defining `multiTwist`. -/
theorem multiTwist_def
    {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) {r : ℕ}
    (L : Fin r → X.Modules) [∀ j : Fin r, isInvertibleObject (L j)]
    (n : Fin r → ℤ) :
    multiTwist F L n =
      (List.finRange r).foldl
        (fun acc j ↦ tensorObj acc (InvertiblePower.obj (L j) (n j))) F :=
  rfl

/-- Tensoring a coherent module on a locally Noetherian algebraic space by a finite
family of invertible powers preserves coherence. -/
instance instIsCoherent_multiTwist
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] {r : ℕ} (L : Fin r → X.Modules)
    [∀ j : Fin r, isInvertibleObject (L j)] (n : Fin r → ℤ) :
    (multiTwist F L n).IsCoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.TensorPower
