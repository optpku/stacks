module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.BivariantClass.ZeroScheme.Commutation

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/- Example 42.33.7: the bivariant Gysin class of the zero scheme of a section of an
invertible module commutes with every bivariant class into the ambient scheme. -/
@[stacks 0FA3] #check
  (AlgebraicGeometry.BivariantClass.gysin_commute :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      {X Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Z.hom]
      (L : X.left.Modules) [Scheme.Modules.Invertible L] (s : L.sections)
      (f : Z ⟶ X) [LocallyOfFiniteType f.left] (p : ℤ) (c : BivariantClass δ f p),
      Commute δ f
        (Over.homMk (Scheme.zeroSchemeι L s) :
          Over.mk (Scheme.zeroSchemeι L s ≫ X.hom) ⟶ X)
        c (gysin δ X L s))

end AlgebraicGeometry.BivariantClass
