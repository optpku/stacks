/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme

/-!
# Étale base change of conormal sheaves

Canonical comparison and naturality of the conormal sheaf of an immersion along
étale scheme charts, with the induced maps between coborder opens.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Conormal

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
variable {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]

/-- The fibre product `Z_U = U ×_X Z`, realised as `pullback i φ`. -/
noncomputable abbrev space : AlgebraicSpace S :=
  pullback i φ

/-- The projection `Z_U ⟶ U`, a locally closed immersion. -/
noncomputable abbrev ι : space i φ ⟶ ofOver U :=
  pullback.snd i φ

/-- The projection `Z_U ⟶ Z` along which `C_{Z/X}` is restricted to `Z_U`. -/
noncomputable abbrev toZ : space i φ ⟶ Z :=
  pullback.fst i φ

/-- The coborder `X \ ∂Z` of `i`, pulled back along the étale chart `φ`. -/
noncomputable abbrev coborderPullback : AlgebraicSpace S :=
  pullback (IsImmersion.coborderRange i).ι φ

/-- Commutativity of the cone presenting `Z_U` over the coborder pullback square. -/
theorem liftToCoborder_w :
    (toZ i φ ≫ IsImmersion.liftCoborder i) ≫ (IsImmersion.coborderRange i).ι = ι i φ ≫ φ :=
  sorry

/-- The closed immersion `Z_U ⟶ U \ φ⁻¹(∂Z)` obtained by pulling back the coborder of `i`. -/
noncomputable def liftToCoborder : space i φ ⟶ coborderPullback i φ :=
  pullback.lift (toZ i φ ≫ IsImmersion.liftCoborder i) (ι i φ) (liftToCoborder_w i φ)

/-- `liftToCoborder` is a closed immersion, as the pullback of the coborder closed immersion. -/
instance instIsClosedImmersion_liftToCoborder : IsClosedImmersion (liftToCoborder i φ) :=
  sorry

/-- The image of the coborder of `ι` lands in the coborder of `i` after composing with `φ`. -/
theorem coborderHom_range_subset {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] :
    Set.range (Points.map ((IsImmersion.coborderRange (ι i φ)).ι ≫ φ)) ⊆
      Set.range (Points.map (IsImmersion.coborderRange i).ι) :=
  sorry

/-- Factorization of `(coborderRange (ι)).ι ≫ φ` through the coborder open of `i`. -/
noncomputable def coborderHom :
    (IsImmersion.coborderRange (ι i φ)).X ⟶ Hom.coborder i :=
  OpenSubspace.Construction.lift
    ((IsImmersion.coborderRange (ι i φ)).ι ≫ φ) (by
      simpa only [IsImmersion.coborderRange, OpenSubspace.fromOpens,
        OpenSubspace.Construction.inclusion_range] using coborderHom_range_subset i φ)

/-- `coborderHom` is the open-immersion factorization of `(coborderRange (ι)).ι ≫ φ`. -/
theorem coborderHom_spec :
    coborderHom i φ ≫ (IsImmersion.coborderRange i).ι =
      (IsImmersion.coborderRange (ι i φ)).ι ≫ φ :=
  OpenSubspace.Construction.lift_ι _ _

/-- The coborder of `ι` maps to the pulled-back coborder of `i` by `pullback.lift`. -/
noncomputable def coborderToPullback :
    (IsImmersion.coborderRange (ι i φ)).X ⟶ coborderPullback i φ :=
  pullback.lift (coborderHom i φ) (IsImmersion.coborderRange (ι i φ)).ι (coborderHom_spec i φ)

/-- The coborder pullback square of the étale chart, as a commutative square of closed
immersions. -/
theorem coborderSq_w :
    toZ i φ ≫ IsImmersion.liftCoborder i =
      liftToCoborder i φ ≫ pullback.fst (IsImmersion.coborderRange i).ι φ :=
  sorry

/-- Identification of the composite `liftCoborder (ι) ≫ coborderToPullback` with
`liftToCoborder`. -/
theorem liftCoborder_ι_comp :
    IsImmersion.liftCoborder (ι i φ) ≫ coborderToPullback i φ = liftToCoborder i φ :=
  sorry

/-- The canonical conormal map of an étale base change of an immersion is invertible. -/
instance instIsIso_restrictEtaleMap :
    IsIso (map (IsPullback.of_hasPullback i φ).toCommSq) :=
  map_isIso_of_isPullback_of_flat (IsPullback.of_hasPullback i φ)

/-- Pullback along an étale scheme chart canonically identifies the conormal sheaf
of an immersion with the conormal sheaf of its base change. -/
noncomputable def restrictEtale :
    (Modules.pullback (toZ i φ)).obj (conormalSheaf i) ≅ conormalSheaf (ι i φ) :=
  asIso (map (IsPullback.of_hasPullback i φ).toCommSq)

/-- The étale conormal comparison has the canonical pullback-square conormal map
as its forward morphism. -/
@[simp]
theorem restrictEtale_hom :
    (restrictEtale i φ).hom = map (IsPullback.of_hasPullback i φ).toCommSq :=
  asIso_hom (map (IsPullback.of_hasPullback i φ).toCommSq)

/-- The pullback of an immersion along an étale scheme chart is a scheme. -/
instance instIsScheme_space {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] :
    IsScheme (space i φ) :=
  sorry

/-- The morphism `Z_U ⟶ Z_V` induced by a morphism of étale charts. -/
noncomputable def spaceMap {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ] (f : ofOver U ⟶ ofOver V)
    (hf : f ≫ ψ = φ) : space i φ ⟶ space i ψ :=
  pullback.map i φ i ψ (𝟙 Z) f (𝟙 X)
    ((Category.comp_id i).trans (Category.id_comp i).symm)
    ((Category.comp_id φ).trans hf.symm)

/-- `spaceMap` commutes with restriction to `Z`. -/
theorem spaceMap_comp_toZ {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ] (f : ofOver U ⟶ ofOver V)
    (hf : f ≫ ψ = φ) : spaceMap i φ ψ f hf ≫ toZ i ψ = toZ i φ :=
  sorry

/-- `spaceMap` commutes with the locally closed immersions into the étale charts. -/
theorem spaceMap_comp_ι {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ] (f : ofOver U ⟶ ofOver V)
    (hf : f ≫ ψ = φ) : spaceMap i φ ψ f hf ≫ ι i ψ = ι i φ ≫ f :=
  sorry

/-- The chart square `Z_U ⟶ Z_V` over `U ⟶ V` of locally closed immersions. -/
theorem chartSq {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ] (f : ofOver U ⟶ ofOver V)
    (hf : f ≫ ψ = φ) : CommSq (spaceMap i φ ψ f hf) (ι i φ) (ι i ψ) f :=
  ⟨spaceMap_comp_ι i φ ψ f hf⟩

/-- Reassociation of successive pullbacks of `C_{Z/X}` along `spaceMap` and `toZ`. -/
noncomputable def restrictEtaleToZReassoc {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (Modules.pullback (spaceMap i φ ψ f hf)).obj
        ((Modules.pullback (toZ i ψ)).obj (conormalSheaf i)) ≅
      (Modules.pullback (toZ i φ)).obj (conormalSheaf i) :=
  (Modules.pullbackCompIso (spaceMap i φ ψ f hf) (toZ i ψ)).app (conormalSheaf i) ≪≫
    (eqToIso (congrArg Modules.pullback (spaceMap_comp_toZ i φ ψ f hf))).app (conormalSheaf i)

/-- The image of the coborder of `ι i φ` lands in the coborder of `ι i ψ` after
composing with the chart morphism `f`. -/
theorem chartCoborderHom_range_subset {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    Set.range (Points.map ((IsImmersion.coborderRange (ι i φ)).ι ≫ f)) ⊆
      Set.range (Points.map (IsImmersion.coborderRange (ι i ψ)).ι) :=
  sorry

/-- The coborder of `ι i φ` maps to the coborder of `ι i ψ` by the open-immersion
factorization of `(coborderRange (ι i φ)).ι ≫ f`. -/
noncomputable def chartCoborderHom {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (IsImmersion.coborderRange (ι i φ)).X ⟶ Hom.coborder (ι i ψ) :=
  OpenSubspace.Construction.lift
    ((IsImmersion.coborderRange (ι i φ)).ι ≫ f) (by
      simpa only [IsImmersion.coborderRange, OpenSubspace.fromOpens,
        OpenSubspace.Construction.inclusion_range] using
          chartCoborderHom_range_subset i φ ψ f hf)

/-- `chartCoborderHom` is the open-immersion factorization of
`(coborderRange (ι i φ)).ι ≫ f`. -/
theorem chartCoborderHom_spec {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    chartCoborderHom i φ ψ f hf ≫ (IsImmersion.coborderRange (ι i ψ)).ι =
      (IsImmersion.coborderRange (ι i φ)).ι ≫ f :=
  OpenSubspace.Construction.lift_ι _ _

/-- `spaceMap` identifies the coborder closed immersions of `ι i φ` and `ι i ψ`
after composing with `chartCoborderHom`. -/
theorem chartLiftCoborder_comp {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    spaceMap i φ ψ f hf ≫ IsImmersion.liftCoborder (ι i ψ) =
      IsImmersion.liftCoborder (ι i φ) ≫ chartCoborderHom i φ ψ f hf :=
  sorry

/-- The identification `C_{Z/X}|_{Z_U} ≅ C_{Z_U/U}` is functorial in morphisms of étale
charts: pullback of `restrictEtale i ψ` along `spaceMap` equals `restrictEtale i φ`
after reassociating pullback to the original immersed space and applying the canonical
conormal map of the chart square. -/
theorem restrictEtale_natural {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ] (f : ofOver U ⟶ ofOver V)
    (hf : f ≫ ψ = φ) :
    (Modules.pullback (spaceMap i φ ψ f hf)).map (restrictEtale i ψ).hom ≫
        map (chartSq i φ ψ f hf) =
      (restrictEtaleToZReassoc i φ ψ f hf).hom ≫ (restrictEtale i φ).hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Conormal
