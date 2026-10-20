module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.ContractionUniqueness
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

noncomputable section

universe u

/- Lemma 109.23.2: A compatible fibre isomorphism of contraction targets extends
over an open neighbourhood when the first fibre morphism has structure-sheaf
pushforward isomorphism and vanishing first higher direct image. -/
@[stacks 0E89] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_open_iso_of_fiber :
    ∀ {S : Scheme.{u}} {X Y1 Y2 : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S)))
    (g1 : Y1 ⟶ ofOver (Over.mk (𝟙 S))) (g2 : Y2 ⟶ ofOver (Over.mk (𝟙 S)))
    [IsFamily f] [IsFamily g1] [IsFamily g2]
    (c1 : X ⟶ Y1) (hc1 : c1 ≫ g1 = f) (c2 : X ⟶ Y2) (hc2 : c2 ≫ g2 = f) (s : S)
    (e_s :
      pullback g1 (ofOverHomMk (S.fromSpecResidueField s) (Category.comp_id _)) ≅
        pullback g2 (ofOverHomMk (S.fromSpecResidueField s) (Category.comp_id _)))
    (h_compat : fiberMap c1 hc1 s ≫ e_s.hom = fiberMap c2 hc2 s)
    (h_unit : IsIso (Modules.unitToPushforwardObjUnit (fiberMap c1 hc1 s)))
    (h_R1 : IsZero (higherDirectImageOne (fiberMap c1 hc1 s))),
    ∃ (U : S.Opens) (hs : s ∈ U)
      (e : pullback g1 (openι U) ≅ pullback g2 (openι U))
      (h_over : e.hom ≫ pullback.snd g2 (openι U) = pullback.snd g1 (openι U)),
      overMap c1 hc1 (openι U) ≫ e.hom = overMap c2 hc2 (openι U) ∧
        restrictsToFiberIso e h_over e_s)
