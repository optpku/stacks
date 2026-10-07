module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.CategoryTheory.Monoidal.InvertiblePower
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal

/-!
# Finite families of tensor twists on algebraic spaces

This leaf packages the ordered tensor product of integral powers of a finite
family of invertible modules on an algebraic space. It is independent of
intersection numbers and can be reused by numerical-polynomial arguments.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A coherent module on a locally Noetherian algebraic space is canonically
quasi-coherent. -/
instance instIsQuasicoherentOfIsCoherent
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] : F.IsQuasicoherent :=
  sorry

namespace TensorPower

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
  sorry

/-- Tensoring a coherent module on a locally Noetherian algebraic space by a finite
family of invertible powers preserves coherence. -/
instance instIsCoherent_multiTwist
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] {r : ℕ} (L : Fin r → X.Modules)
    [∀ j : Fin r, isInvertibleObject (L j)] (n : Fin r → ℤ) :
    (multiTwist F L n).IsCoherent :=
  sorry

end TensorPower

end AlgebraicGeometry.AlgebraicSpace.Modules
