module

public import ReasLib.Topology.Sheaves.Ring.Definition

@[expose] public section

/-!
# Pullback of underlying ring sheaves

This file owns the comparison between pullback of a sheaf of commutative rings followed by
forgetting commutativity, and pullback of its underlying sheaf of rings.
-/

open CategoryTheory TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

/-- Pullback of a sheaf of commutative rings commutes with passage to its underlying sheaf of
rings, provided the target site preserves sheafification under the forgetful functor. -/
noncomputable abbrev ringSheafOfCommPullbackIso
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    [(Opens.grothendieckTopology Y).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    (O : X.Sheaf CommRingCat.{u}) :
    (sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat.{u})).obj
        ((pullback CommRingCat.{u} f).obj O) ≅
      (pullback RingCat.{u} f).obj
        ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat RingCat.{u})).obj O) :=
  let RO : X.Sheaf RingCat.{u} :=
    (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat RingCat.{u})).obj O
  let P : (Opens Y)ᵒᵖ ⥤ CommRingCat.{u} :=
    (TopCat.Presheaf.pullback CommRingCat.{u} f).obj O.1
  let h₁ :
      (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).obj
          ((presheafToSheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).obj P) ≅
        (presheafToSheaf (Opens.grothendieckTopology Y) RingCat.{u}).obj
          (P ⋙ forget₂ CommRingCat RingCat.{u}) :=
    ((CategoryTheory.sheafComposeNatIso
        (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat.{u})
        (CategoryTheory.sheafificationAdjunction
          (Opens.grothendieckTopology Y) CommRingCat.{u})
        (CategoryTheory.sheafificationAdjunction
          (Opens.grothendieckTopology Y) RingCat.{u})).app P).symm
  let h₂ :
      (presheafToSheaf (Opens.grothendieckTopology Y) RingCat.{u}).obj
          (P ⋙ forget₂ CommRingCat RingCat.{u}) ≅
        (forget RingCat.{u} X ⋙ TopCat.Presheaf.pullback RingCat.{u} f ⋙
            presheafToSheaf (Opens.grothendieckTopology Y) RingCat.{u}).obj RO := by
    let hP :
        P ⋙ forget₂ CommRingCat RingCat.{u} ≅
          (TopCat.Presheaf.pullback RingCat.{u} f).obj RO.1 := by
      simpa [P, RO, TopCat.Presheaf.pullback] using
        ((Functor.lanCompIsoOfPreserves
          (L := (Opens.map f).op)
          (G := forget₂ CommRingCat RingCat.{u})).app O.1)
    exact (presheafToSheaf (Opens.grothendieckTopology Y) RingCat.{u}).mapIso hP
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).mapIso
      ((TopCat.Sheaf.pullbackIso CommRingCat.{u} f).app O) ≪≫
    h₁ ≪≫
    h₂ ≪≫
    ((TopCat.Sheaf.pullbackIso RingCat.{u} f).app RO).symm

/-- The pullback comparison for commutative-ring sheaves carries the underlying commutative
pullback unit to the ordinary RingCat-valued pullback unit. -/
@[stacks 03D6 "compatibility of commutative pullback with the adjunction unit"]
theorem ringSheafOfCommPullbackIso_unit
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    [(Opens.grothendieckTopology Y).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    (O : X.Sheaf CommRingCat.{u}) :
    commRingSheafPullbackUnit f O ≫
        ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map
          (ringSheafOfCommPullbackIso f O).hom =
      (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app
        (ringSheafOfComm O) := sorry

end TopCat.Sheaf
