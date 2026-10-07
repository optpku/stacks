module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.RingTheory.Henselian

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a proper scheme over a henselian local ring, first étale cohomology
with finite constant abelian coefficients is isomorphic to the corresponding
cohomology of the closed fibre. -/
theorem etaleH1IsomorphicOfProperHenselian
    {A : Type u} [CommRing A] [HenselianLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (M : AddCommGrpCat.{u})
    [Finite M]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify
      (f.fiber (IsLocalRing.closedPoint A)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u}
      (Sheaf (f.fiber (IsLocalRing.closedPoint A)).smallEtaleTopology
        AddCommGrpCat.{u})] :
    IsIsomorphic
      ((Sheaf.functorH X.smallEtaleTopology 1).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj M))
      ((Sheaf.functorH
          (f.fiber (IsLocalRing.closedPoint A)).smallEtaleTopology 1).obj
        ((constantSheaf
            (f.fiber (IsLocalRing.closedPoint A)).smallEtaleTopology
            AddCommGrpCat.{u}).obj M)) := sorry

end AlgebraicGeometry.Scheme.Hom
