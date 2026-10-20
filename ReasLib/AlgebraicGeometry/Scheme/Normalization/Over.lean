module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Components
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Absolute normalization of schemes over a base

Normalization and generic-point-preserving morphisms are regarded in the slice over a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Normalization

/-- The scheme over `S` represented by the absolute normalization of `U`. -/
def overNormalization {S : Scheme.{u}} (U : Over S)
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left] : Over S :=
  Over.mk (U.left.normalizationTo ≫ U.hom)

/-- The morphism of schemes over `S` induced by the absolute normalization of `U`. -/
def overNormalizationTo {S : Scheme.{u}} (U : Over S)
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left] :
    overNormalization U ⟶ U :=
  Over.homMk U.left.normalizationTo rfl

/-- The underlying scheme of `overNormalization U` is the absolute normalization of `U`. -/
theorem overNormalization_left {S : Scheme.{u}} (U : Over S)
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left] :
    (overNormalization U).left = U.left.normalization :=
  rfl

/-- An étale morphism of schemes sends generic points to generic points. -/
theorem mapsTo_genericPoints_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.Etale f] :
    Set.MapsTo f (genericPoints X) (genericPoints Y) :=
  sorry

/-- Composing the absolute normalization morphism with a generic-point-preserving map
still sends generic points to generic points. -/
theorem mapsTo_genericPoints_normalizationTo_comp {X Y : Scheme.{u}}
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] (f : X ⟶ Y)
    (hf : Set.MapsTo f (genericPoints X) (genericPoints Y)) :
    Set.MapsTo (X.normalizationTo ≫ f) (genericPoints X.normalization) (genericPoints Y) :=
  sorry

/-- The coproduct of residue-field spectra is functorial in generic-point-preserving
morphisms of schemes. -/
def genericPointSpectrumCoproductMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Set.MapsTo f (genericPoints X) (genericPoints Y)) :
    genericPointSpectrumCoproduct X ⟶ genericPointSpectrumCoproduct Y :=
  Sigma.desc fun η : genericPoints X ↦
    Spec.map (Scheme.Hom.residueFieldMap f η.1) ≫
      Sigma.ι (fun ξ : genericPoints Y ↦ Spec (Y.residueField ξ.1)) ⟨f η.1, hf η.2⟩

/-- `genericPointSpectrumCoproductMap f hf` is the coproduct descent of the residue-field
maps of `f` on generic points. -/
theorem genericPointSpectrumCoproductMap_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Set.MapsTo f (genericPoints X) (genericPoints Y)) :
    genericPointSpectrumCoproductMap f hf =
      Sigma.desc fun η : genericPoints X ↦
        Spec.map (Scheme.Hom.residueFieldMap f η.1) ≫
          Sigma.ι (fun ξ : genericPoints Y ↦ Spec (Y.residueField ξ.1)) ⟨f η.1, hf η.2⟩ :=
  rfl

/-- The coproduct map of residue-field spectra intertwines the canonical morphisms to the
underlying schemes. -/
theorem genericPointSpectrumCoproductMap_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Set.MapsTo f (genericPoints X) (genericPoints Y)) :
    genericPointSpectrumCoproductMap f hf ≫ genericPointSpectrumCoproductTo Y =
      genericPointSpectrumCoproductTo X ≫ f :=
  sorry

/-- The two legs of the comparison cone to `U ×_V V^ν` agree over `V`. -/
theorem overNormalizationToPullback_lift_comm {S : Scheme.{u}} {U V : Over S}
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens V.left]
    (g : U ⟶ V)
    (hg : Set.MapsTo g.left (genericPoints U.left) (genericPoints V.left)) :
    genericPointSpectrumCoproductMap g.left hg ≫
          (genericPointSpectrumCoproductTo V.left).toNormalization ≫
            V.left.normalizationTo =
      genericPointSpectrumCoproductTo U.left ≫ g.left :=
  sorry

/-- The second projection of the comparison lift recovers the coproduct map of `U`. -/
theorem overNormalizationToPullback_lift_snd {S : Scheme.{u}} {U V : Over S}
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens V.left]
    (g : U ⟶ V)
    (hg : Set.MapsTo g.left (genericPoints U.left) (genericPoints V.left)) :
    pullback.lift
          (genericPointSpectrumCoproductMap g.left hg ≫
            (genericPointSpectrumCoproductTo V.left).toNormalization)
          (genericPointSpectrumCoproductTo U.left)
          (overNormalizationToPullback_lift_comm g hg) ≫
        pullback.snd V.left.normalizationTo g.left =
      genericPointSpectrumCoproductTo U.left :=
  sorry

/-- The comparison morphism from `U^ν` to the one-sided fibre product `U ×_V V^ν`
along a generic-point-preserving morphism `g`. -/
def overNormalizationToPullback_left {S : Scheme.{u}} {U V : Over S}
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens V.left]
    (g : U ⟶ V)
    (hg : Set.MapsTo g.left (genericPoints U.left) (genericPoints V.left)) :
    U.left.normalization ⟶ pullback V.left.normalizationTo g.left :=
  (genericPointSpectrumCoproductTo U.left).normalizationDesc
    (pullback.lift
      (genericPointSpectrumCoproductMap g.left hg ≫
        (genericPointSpectrumCoproductTo V.left).toNormalization)
      (genericPointSpectrumCoproductTo U.left)
      (overNormalizationToPullback_lift_comm g hg))
    (pullback.snd V.left.normalizationTo g.left)
    (overNormalizationToPullback_lift_snd g hg).symm

/-- The unique lift of a generic-point-preserving morphism of schemes over `S` through
absolute normalization, as a morphism of schemes. -/
def overNormalizationMap_left {S : Scheme.{u}} {U V : Over S}
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens V.left]
    (g : U ⟶ V)
    (hg : Set.MapsTo g.left (genericPoints U.left) (genericPoints V.left)) :
    U.left.normalization ⟶ V.left.normalization :=
  overNormalizationToPullback_left g hg ≫ pullback.fst V.left.normalizationTo g.left

/-- `overNormalizationMap_left g hg` is compatible with the structure morphisms to `S`. -/
theorem overNormalizationMap_w {S : Scheme.{u}} {U V : Over S}
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens V.left]
    (g : U ⟶ V)
    (hg : Set.MapsTo g.left (genericPoints U.left) (genericPoints V.left)) :
    overNormalizationMap_left g hg ≫ (overNormalization V).hom =
      (overNormalization U).hom :=
  sorry

/-- The unique lift of a generic-point-preserving morphism of schemes over `S` through
absolute normalization. -/
def overNormalizationMap {S : Scheme.{u}} {U V : Over S}
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens V.left]
    (g : U ⟶ V)
    (hg : Set.MapsTo g.left (genericPoints U.left) (genericPoints V.left)) :
    overNormalization U ⟶ overNormalization V :=
  Over.homMk (overNormalizationMap_left g hg) (overNormalizationMap_w g hg)

/-- The lifted morphism sits over `g` after composing with the absolute normalization
morphisms. -/
theorem overNormalizationMap_comp {S : Scheme.{u}} {U V : Over S}
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens V.left]
    (g : U ⟶ V)
    (hg : Set.MapsTo g.left (genericPoints U.left) (genericPoints V.left)) :
    overNormalizationMap g hg ≫ overNormalizationTo V =
      overNormalizationTo U ≫ g :=
  sorry

/-- The unique lift of a generic-point-preserving morphism of schemes over `S` through
absolute normalization exists. -/
theorem existsUnique_overNormalizationMap_of_mapsTo {S : Scheme.{u}} {U V : Over S}
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens V.left]
    (g : U ⟶ V)
    (hg : Set.MapsTo g.left (genericPoints U.left) (genericPoints V.left)) :
    ∃! f : overNormalization U ⟶ overNormalization V,
      f ≫ overNormalizationTo V = overNormalizationTo U ≫ g := by
  have hnormal : U.left.normalization.isNormal :=
    Scheme.HasPairwiseDisjointOpenCoverByNormalIntegral.isNormal (cover U.left)
  sorry

end AlgebraicGeometry.Scheme.Normalization
