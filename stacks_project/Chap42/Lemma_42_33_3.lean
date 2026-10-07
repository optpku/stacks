module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.BivariantClass.ZeroScheme

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 42.33.3: Gysin pullback along the zero scheme of a section of an invertible
module defines a bivariant Chow class of degree one. -/
@[stacks 0B79] #check
  (AlgebraicGeometry.BivariantClass.gysin :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (X : Over S) [LocallyOfFiniteType X.hom]
      (L : X.left.Modules) [Scheme.Modules.Invertible L] (s : L.sections),
      BivariantClass δ
        (Over.homMk (Scheme.zeroSchemeι L s) :
          Over.mk (Scheme.zeroSchemeι L s ≫ X.hom) ⟶ X) 1)

#check
  (AlgebraicGeometry.BivariantClass.gysin_cap :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (X : Over S) [LocallyOfFiniteType X.hom]
      (L : X.left.Modules) [Scheme.Modules.Invertible L] (s : L.sections)
      {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
      (i : X' ⟶ Over.mk (Scheme.zeroSchemeι L s ≫ X.hom)) (f' : X' ⟶ Y')
      (g : Y' ⟶ X) [LocallyOfFiniteType g.left]
      (square : IsPullback i.left f'.left
        (Over.homMk (Scheme.zeroSchemeι L s) :
          Over.mk (Scheme.zeroSchemeι L s ≫ X.hom) ⟶ X).left g.left)
      (k : ℤ),
      (BivariantClass.gysin δ X L s).cap i f' g square k =
        (ChowGroup.map δ
          (Over.mk
            (Scheme.zeroSchemeι ((Scheme.Modules.pullback g.left).obj L)
              (Scheme.Modules.sectionsPullback g.left L s) ≫ Y'.hom))
          X' (BivariantClass.gysinBaseChangeIso L s i f' g square).hom (k - 1)).comp
          (ChowGroup.gysin δ Y' ((Scheme.Modules.pullback g.left).obj L)
            (Scheme.Modules.sectionsPullback g.left L s) k))
