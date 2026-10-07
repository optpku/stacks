module

import ReasLib.AlgebraicGeometry.Scheme.Sites.H.EssentialImage
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.GrothendieckTopology
open CategoryTheory.GrothendieckTopology.Derived
open CategoryTheory.GrothendieckTopology.Derived.Sections.MayerVietoris

universe u

/- Lemma 59.106.3: for a bounded-below derived object `K` on the fppf site over
`S`, membership in the essential image of `Rε_*` is equivalent to the
Mayer–Vietoris condition on every square in one of the two canonical
almost-blowup families. -/
@[stacks 0EWR] #check
  (AlgebraicGeometry.Scheme.H.essImage_iff_exampleAlmostBlowupCondition :
    ∀ {S : Scheme.{u}}
      (hle : Scheme.fppfTopology.over S ≤
        (Scheme.hPrecoverage.toGrothendieck).over S)
      [HasSheafify ((Scheme.hPrecoverage.toGrothendieck).over S)
        AddCommGrpCat.{u + 1}]
      [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}]
      [IsGrothendieckAbelian.{u + 1}
        (SiteAbelianSheafCat (Scheme.fppfTopology.over S))]
      [HasWeakSheafify ((Scheme.hPrecoverage.toGrothendieck).over S)
        (Type (u + 1))]
      [Functor.HasRightDerivedFunctor
        (Functor.Homotopy.toDerived (Absolute.pushforward hle))
        (Absolute.qis ((Scheme.hPrecoverage.toGrothendieck).over S))]
      (K : DerivedCategory.Plus (SiteAbelianSheafCat (Scheme.fppfTopology.over S))),
      Functor.essImage
          (Absolute.rightDerived hle)
          (DerivedCategory.Plus.ι.obj K) ↔
        ∀ (sq :
          CategoryTheory.GrothendieckTopology.Derived.Sections.MayerVietoris.Square
            (Over S)),
          AlgebraicGeometry.Scheme.H.IsExampleAlmostBlowupSquare sq →
          sq.Condition (Scheme.fppfTopology.over S) (DerivedCategory.Plus.ι.obj K))
