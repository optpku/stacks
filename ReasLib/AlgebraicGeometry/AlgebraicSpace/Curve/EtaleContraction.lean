module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Family
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback.OverMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Hom
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood

/-!
# Étale-local contraction of a fibre morphism of a family of curves

Given a family of curves over a scheme and a contraction of one fibre onto a
proper scheme over the residue field, with structure-sheaf unit an isomorphism
and vanishing `R¹`, the contraction spreads out after an elementary étale
base change of the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The morphism of algebraic spaces over `S` induced by `S.fromSpecResidueField s`. -/
abbrev residueHom {S : Scheme.{u}} (s : S) :
    ofOver (Over.mk (S.fromSpecResidueField s)) ⟶ ofOver (Over.mk (𝟙 S)) :=
  ofOverHomMk (S.fromSpecResidueField s) (Category.comp_id _)

/-- `residueHom s` is `ofOverHomMk` of `S.fromSpecResidueField s`. -/
theorem residueHom_eq {S : Scheme.{u}} (s : S) :
    residueHom s = ofOverHomMk (S.fromSpecResidueField s) (Category.comp_id _) :=
  rfl

/-- The morphism of algebraic spaces over `S` induced by an étale neighbourhood. -/
abbrev etaleHom {S : Scheme.{u}} {s : S} (U : Scheme.EtaleNeighborhood S s) :
    ofOver (Over.mk U.toEtale.hom) ⟶ ofOver (Over.mk (𝟙 S)) :=
  ofOverHomMk U.toEtale.hom (Category.comp_id _)

/-- `etaleHom U` is `ofOverHomMk` of the structure morphism of `U`. -/
theorem etaleHom_eq {S : Scheme.{u}} {s : S} (U : Scheme.EtaleNeighborhood S s) :
    etaleHom U = ofOverHomMk U.toEtale.hom (Category.comp_id _) :=
  rfl

/-- The residue-point map of an étale neighbourhood, viewed as a morphism of
algebraic spaces over `S`. -/
abbrev pointHom {S : Scheme.{u}} {s : S} (U : Scheme.EtaleNeighborhood S s) :
    ofOver (Over.mk (U.toEtale.left.fromSpecResidueField U.point ≫ U.toEtale.hom)) ⟶
      ofOver (Over.mk U.toEtale.hom) :=
  ofOverHomMk (U.toEtale.left.fromSpecResidueField U.point) rfl

/-- `pointHom U` is `ofOverHomMk` of `fromSpecResidueField` at the selected point. -/
theorem pointHom_eq {S : Scheme.{u}} {s : S} (U : Scheme.EtaleNeighborhood S s) :
    pointHom U =
      ofOverHomMk (U.toEtale.left.fromSpecResidueField U.point) rfl :=
  rfl

/-- The spectrum map of the residue-field homomorphism of an étale neighbourhood
of `(S, s)`, after identifying the image point with `s`, is a morphism over `S`. -/
theorem residueFieldMap_over {S : Scheme.{u}} {s : S}
    (U : Scheme.EtaleNeighborhood S s) :
    (Spec.map (U.toEtale.hom.residueFieldMap U.point) ≫
        Spec.map (S.residueFieldCongr U.map_point).inv) ≫
      S.fromSpecResidueField s =
      U.toEtale.left.fromSpecResidueField U.point ≫ U.toEtale.hom :=
  sorry

/-- Let `f : X ⟶ S` be a family of curves, `s` a point of `S`, and
`h₀ : X_s ⟶ Y₀` a morphism to a proper scheme `Y₀` over `κ(s)` such that
`Modules.unitToPushforwardObjUnit h₀` is an isomorphism and
`higherDirectImageOne h₀` vanishes. Then there exist an elementary étale
neighbourhood `(U, u) → (S, s)`, a family of curves `g : Y ⟶ U`, and a
morphism `h : X_U ⟶ Y` over `U` whose fibre at `u` is isomorphic to `h₀`
under the canonical source-fibre identification, with the target comparison
commuting with the canonical residue-field map. -/
theorem exists_elementaryEtale_contraction
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) [IsFamily f] (s : S)
    (Y₀ : Scheme.{u}) (q₀ : Y₀ ⟶ Spec (S.residueField s)) [IsProper q₀]
    (h₀ : pullback f (residueHom s) ⟶
      ofOver (Over.mk (q₀ ≫ S.fromSpecResidueField s)))
    (h₀_over : h₀ ≫ ofOverHomMk q₀ rfl = pullback.snd f (residueHom s))
    (h_unit : IsIso (Modules.unitToPushforwardObjUnit h₀))
    (h_R1 : IsZero (higherDirectImageOne h₀)) :
    ∃ (U : Scheme.EtaleNeighborhood S s) (Y : AlgebraicSpace S)
      (g : Y ⟶ ofOver (Over.mk U.toEtale.hom))
      (h : pullback f (etaleHom U) ⟶ Y),
      U.IsElementary ∧ IsFamily g ∧
        ∃ (h_over : h ≫ g = pullback.snd f (etaleHom U))
          (iX : pullback (pullback.snd f (etaleHom U)) (pointHom U) ≅
            pullback f (residueHom s))
          (iY : pullback g (pointHom U) ≅
            ofOver (Over.mk (q₀ ≫ S.fromSpecResidueField s))),
          iX.hom ≫ pullback.snd f (residueHom s) =
              pullback.snd (pullback.snd f (etaleHom U)) (pointHom U) ≫
                ofOverHomMk
                  (Spec.map (U.toEtale.hom.residueFieldMap U.point) ≫
                    Spec.map (S.residueFieldCongr U.map_point).inv)
                  (residueFieldMap_over U) ∧
            iX.hom ≫ pullback.fst f (residueHom s) =
              pullback.fst (pullback.snd f (etaleHom U)) (pointHom U) ≫
                pullback.fst f (etaleHom U) ∧
            iY.hom ≫ ofOverHomMk q₀ rfl =
              pullback.snd g (pointHom U) ≫
                ofOverHomMk
                  (Spec.map (U.toEtale.hom.residueFieldMap U.point) ≫
                    Spec.map (S.residueFieldCongr U.map_point).inv)
                  (residueFieldMap_over U) ∧
            iX.hom ≫ h₀ = overMap h h_over (pointHom U) ≫ iY.hom :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
