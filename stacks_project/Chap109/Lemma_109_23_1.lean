module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.ContractionNeighborhood
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback.OverMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Hom
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

universe u

/- Lemma 109.23.1 -/
@[stacks 0E88] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_open_of_fiber :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      (f : X ⟶ ofOver (Over.mk (𝟙 S))) (g : Y ⟶ ofOver (Over.mk (𝟙 S)))
      [IsFamily f] [IsFamily g] (c : X ⟶ Y) (hc : c ≫ g = f) (s : S),
      IsIso (Modules.unitToPushforwardObjUnit (fiberMap c hc s)) →
        IsZero (higherDirectImageOne (fiberMap c hc s)) →
          ∃ U : S.Opens, s ∈ U ∧
            ∀ {Z : AlgebraicSpace S} (φ : Z ⟶ ofOver (Over.mk U.ι)),
              IsIso (Modules.unitToPushforwardObjUnit (overMap c hc (φ ≫ openι U))) ∧
                IsZero (higherDirectImageOne (overMap c hc (φ ≫ openι U))))
