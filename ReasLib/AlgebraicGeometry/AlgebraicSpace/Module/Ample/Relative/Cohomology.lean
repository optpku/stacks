module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.VanishingH1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.CategoryTheory.MonoidalCategory.TensorPower

/-!
# Relative ampleness and cohomological vanishing

Relative ampleness of an invertible module on a proper algebraic space over a
Noetherian ring is equivalent to eventual vanishing of positive-degree
cohomology of every coherent twist.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An invertible module on an algebraic space proper over a Noetherian ring is
relatively ample if and only if every coherent module, after twisting by all
sufficiently large tensor powers, has zero cohomology in every positive degree,
with a single bound for all positive degrees. -/
@[stacks 0D38]
theorem relativelyAmple_iff_twist_cohomology_eventually_isZero
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper f]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    (L : X.Modules) [isInvertibleObject L] :
    RelativelyAmple f L ↔
      ∀ F : X.Modules, F.IsCoherent →
        ∃ n0 : ℕ, ∀ n, n0 ≤ n → ∀ p, 0 < p →
          IsZero (cohomology X (F ⊗ tensorPower L n) p) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
