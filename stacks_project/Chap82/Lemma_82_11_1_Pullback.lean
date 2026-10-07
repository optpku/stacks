module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Lemma_67_30_4_Pullback
public import stacks_project.Chap68.Definition_68_25_4_UniversallyCatenary
public import stacks_project.Chap76.Lemma_76_32_2
public import stacks_project.Chap82.Definition_82_3_1_CycleGroup
import stacks_project.Chap82.Lemma_82_10_4_Pullback

/-!
# Base change of relative dimension and left-leg flatness

Exact relative dimension of morphisms of algebraic spaces, and flatness of the
chosen left projection, are stable under arbitrary base change. This module
records the `IsPullback` transfer for `RelativeDimension` in the same
orientation as `Flat.of_isPullback`, together with the missing
`pullback.fst` instances.

The cycle-level flat pullback is re-exported without the public
`Lemma_82_10_4_Pullback` import, which collides with
`Lemma_82_8_2_Pushforward` on `Hom.comp_structureMorphism_eq`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

@[expose] public section

namespace RelativeDimension

/-- Exact relative dimension is stable under pullback along an arbitrary
morphism, expressed by an `IsPullback` square. The orientation matches
`Flat.of_isPullback`: the right-hand leg `g` transfers to the left-hand
leg `g'`. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X} {r : ℕ}
    (sq : IsPullback f' g' g f) (hg : RelativeDimension g r) :
    RelativeDimension g' r :=
  sorry

/-- The base-change projection `pullback.fst f g` of a morphism of relative
dimension `r` is of relative dimension `r`. -/
theorem pullback_fst {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {g : Z ⟶ Y}
    {r : ℕ} (hg : RelativeDimension g r) (f : X ⟶ Y) [HasPullback f g] :
    RelativeDimension (pullback.fst f g) r :=
  sorry

end RelativeDimension

/-- Typeclass form of base-change stability for exact relative dimension along
the first projection of a pullback. -/
instance relativeDimension_pullback_fst {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y) (r : ℕ)
    [RelativeDimension g r] [HasPullback f g] :
    RelativeDimension (pullback.fst f g) r :=
  sorry

namespace Flat

/-- The base-change projection `pullback.fst f g` of a flat morphism is
flat. -/
theorem pullback_fst {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {g : Z ⟶ Y}
    (hg : Flat g) (f : X ⟶ Y) [HasPullback f g] : Flat (pullback.fst f g) :=
  sorry

end Flat

/-- Typeclass form of base-change stability for a flat morphism along the
first projection of a pullback. -/
instance flat_pullback_fst {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Flat g] [HasPullback f g] :
    Flat (pullback.fst f g) :=
  sorry

end

public section

noncomputable section

namespace Hom

/-- Flat pullback of `k`-cycles along a morphism of relative dimension `r`, as
an additive map `Z_k(Y) →+ Z_{k + r}(X)`. This is definitionally
`flatPullbackHom`, isolated so cartesian compatibility can import proper
pushforward. -/
noncomputable def cycleFlatPullback {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) :
    (cycleGroup pY) δ k →+ (cycleGroup pX) δ (k + (r : ℤ)) :=
  flatPullbackHom pY pX δ f r hf k

/-- Canonical flat pullback of the zero cycle is zero. -/
theorem cycleFlatPullback_zero {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) :
    cycleFlatPullback pY pX δ f r hf k 0 = 0 :=
  sorry

end Hom

end

end

end AlgebraicGeometry.AlgebraicSpace
