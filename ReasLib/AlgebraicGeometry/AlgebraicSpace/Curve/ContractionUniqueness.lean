module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Family
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback.OverMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Hom
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Spreading a fibre isomorphism of contraction targets

If two morphisms of curve families over a scheme agree up to a fibre
isomorphism, and one of them is a cohomological contraction on that fibre,
then the fibre isomorphism spreads to an isomorphism of families over an
open neighbourhood of the point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- An isomorphism `e` of restricted families over an open `U` recovers the
given fibre isomorphism `e_s` after every factorization of
`Spec κ(s) ⟶ S` through `U`. -/
def restrictsToFiberIso {S : Scheme.{u}} {Y1 Y2 : AlgebraicSpace S}
    {g1 : Y1 ⟶ ofOver (Over.mk (𝟙 S))} {g2 : Y2 ⟶ ofOver (Over.mk (𝟙 S))}
    {U : S.Opens} {s : S}
    (e : pullback g1 (openι U) ≅ pullback g2 (openι U))
    (h_over : e.hom ≫ pullback.snd g2 (openι U) = pullback.snd g1 (openι U))
    (e_s :
      pullback g1 (ofOverHomMk (S.fromSpecResidueField s) (Category.comp_id _)) ≅
        pullback g2 (ofOverHomMk (S.fromSpecResidueField s) (Category.comp_id _))) :
    Prop :=
  ∀ (σ : ofOver (Over.mk (S.fromSpecResidueField s)) ⟶ ofOver (Over.mk U.ι))
    (hσ : σ ≫ openι U =
      ofOverHomMk (S.fromSpecResidueField s) (Category.comp_id _)),
    (pullbackLeftPullbackSndIso g1 (openι U) σ).hom ≫
        (pullback.congrHom (Eq.refl g1) hσ).hom ≫ e_s.hom =
      overMap e.hom h_over σ ≫
        (pullbackLeftPullbackSndIso g2 (openι U) σ).hom ≫
          (pullback.congrHom (Eq.refl g2) hσ).hom

/-- `restrictsToFiberIso e h_over e_s` holds if and only if every
factorization of `Spec κ(s) ⟶ S` through `U` recovers `e_s` from `e`
after pasting and `pullback.congrHom`. -/
theorem restrictsToFiberIso_iff {S : Scheme.{u}} {Y1 Y2 : AlgebraicSpace S}
    {g1 : Y1 ⟶ ofOver (Over.mk (𝟙 S))} {g2 : Y2 ⟶ ofOver (Over.mk (𝟙 S))}
    {U : S.Opens} {s : S}
    (e : pullback g1 (openι U) ≅ pullback g2 (openι U))
    (h_over : e.hom ≫ pullback.snd g2 (openι U) = pullback.snd g1 (openι U))
    (e_s :
      pullback g1 (ofOverHomMk (S.fromSpecResidueField s) (Category.comp_id _)) ≅
        pullback g2 (ofOverHomMk (S.fromSpecResidueField s) (Category.comp_id _))) :
    restrictsToFiberIso e h_over e_s ↔
      ∀ (σ : ofOver (Over.mk (S.fromSpecResidueField s)) ⟶ ofOver (Over.mk U.ι))
        (hσ : σ ≫ openι U =
          ofOverHomMk (S.fromSpecResidueField s) (Category.comp_id _)),
        (pullbackLeftPullbackSndIso g1 (openι U) σ).hom ≫
            (pullback.congrHom (Eq.refl g1) hσ).hom ≫ e_s.hom =
          overMap e.hom h_over σ ≫
            (pullbackLeftPullbackSndIso g2 (openι U) σ).hom ≫
              (pullback.congrHom (Eq.refl g2) hσ).hom :=
  Iff.rfl

/-- Let `S` be a scheme and `s` a point of `S`. Let
`f : X ⟶ ofOver (Over.mk (𝟙 S))` and `g1`, `g2` be families of curves,
and let `c1 : X ⟶ Y1`, `c2 : X ⟶ Y2` be morphisms over `S`. Assume there
is an isomorphism of fibres `e_s` compatible with `fiberMap c1 hc1 s` and
`fiberMap c2 hc2 s`. If `Modules.unitToPushforwardObjUnit (fiberMap c1 hc1 s)`
is an isomorphism and `higherDirectImageOne (fiberMap c1 hc1 s)` is zero,
then there exist an open neighbourhood `U` of `s` and an isomorphism `e`
of the restricted families `pullback g1 (openι U)` and
`pullback g2 (openι U)` over `U`, compatible with `c1`, `c2`, and `e_s`. -/
@[stacks 0E89]
theorem exists_open_iso_of_fiber {S : Scheme.{u}} {X Y1 Y2 : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S)))
    (g1 : Y1 ⟶ ofOver (Over.mk (𝟙 S))) (g2 : Y2 ⟶ ofOver (Over.mk (𝟙 S)))
    [IsFamily f] [IsFamily g1] [IsFamily g2]
    (c1 : X ⟶ Y1) (hc1 : c1 ≫ g1 = f) (c2 : X ⟶ Y2) (hc2 : c2 ≫ g2 = f) (s : S)
    (e_s :
      pullback g1 (ofOverHomMk (S.fromSpecResidueField s) (Category.comp_id _)) ≅
        pullback g2 (ofOverHomMk (S.fromSpecResidueField s) (Category.comp_id _)))
    (h_compat : fiberMap c1 hc1 s ≫ e_s.hom = fiberMap c2 hc2 s)
    (h_unit : IsIso (Modules.unitToPushforwardObjUnit (fiberMap c1 hc1 s)))
    (h_R1 : IsZero (higherDirectImageOne (fiberMap c1 hc1 s))) :
    ∃ (U : S.Opens) (hs : s ∈ U)
      (e : pullback g1 (openι U) ≅ pullback g2 (openι U))
      (h_over : e.hom ≫ pullback.snd g2 (openι U) = pullback.snd g1 (openι U)),
      overMap c1 hc1 (openι U) ≫ e.hom = overMap c2 hc2 (openι U) ∧
        restrictsToFiberIso e h_over e_s :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
