module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow

/-! The Chow Gysin map of a zero scheme commutes with first-Chern cap. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The Chow Gysin map of the zero scheme of a section of an invertible module
commutes with first-Chern cap by an invertible module, with that module pulled
back to the zero scheme on the right-hand side. Both compositions lower the
Chow degree by two. -/
@[stacks 0ERB]
theorem chowGysin_firstChernCap {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L : X.Modules) [isInvertibleObject L] (s : L.sections)
    (N : X.Modules) [isInvertibleObject N]
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L s)).obj N)]
    (k : ℤ) (α : chowGroup f δ (k + 1 + 1)) :
    chowGysin δ f L s k (FirstChernChow.cap f δ N (k + 1) α) =
      FirstChernChow.cap (zeroSchemeι L s ≫ f) δ
        ((Modules.pullback (zeroSchemeι L s)).obj N) k
        (chowGysin δ f L s (k + 1) α) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
