module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace.Twist
public import ReasLib.CategoryTheory.MonoidalCategory.TensorPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- For a closed immersion into projective space over a Noetherian algebraic space,
all positive higher direct images of a coherent module vanish after sufficiently large
powers of the pulled-back degree-one twisting sheaf, with one bound for all degrees. -/
@[stacks 08AQ]
theorem higherDirectImage_projectiveTwist_eventually_isZero
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (n : ℕ)
    (i : X ⟶ ProjectiveSpace n Y) [IsClosedImmersion i] [IsNoetherian Y]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (F : X.Modules) [F.IsCoherent] :
    ∃ d0 : ℕ, ∀ d : ℕ, d0 ≤ d → ∀ p : ℕ, 0 < p →
      IsZero
        (higherDirectImage (i ≫ ProjectiveSpace.toBase n Y)
          (F ⊗ tensorPower ((pullback i).obj (ProjectiveSpace.twistingSheaf n Y)) d) p) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
