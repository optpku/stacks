/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Dominant.FiniteComponents

/-!
# Rational maps preserving generic points of components

This file defines rational maps that carry the generic points of the source
components exactly onto the generic points of the target components.  For
schemes with finitely many irreducible components on quasi-compact opens,
these maps have a composition without an irreducibility assumption.
-/

@[expose] public section

open CategoryTheory hiding Quotient
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {W X Y Z : Scheme.{u}}

namespace PartialMap

private theorem genericPoints_image_homOfLE
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    {U V : X.Opens} (hU : Dense (U : Set X)) (hV : Dense (V : Set X))
    (h : U ≤ V) :
    (X.homOfLE h).base '' genericPoints U = genericPoints V := by
  apply (inferInstance : IsOpenImmersion V.ι).base_open.injective.image_injective
  calc
    V.ι.base '' ((X.homOfLE h).base '' genericPoints U) =
        U.ι.base '' genericPoints U := by
      rw [← Set.image_comp]
      congr 1
      funext x
      exact congr($(X.homOfLE_ι h) x)
    _ = V.ι.base '' genericPoints V :=
      (Opens.genericPointsInAmbient_eq_of_dense U hU).trans
        (Opens.genericPointsInAmbient_eq_of_dense V hV).symm

private theorem genericPoints_subset_dense_open
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : X.Opens) (hU : Dense (U : Set X)) : genericPoints X ⊆ U := by
  rw [← Opens.genericPointsInAmbient_eq_of_dense U hU]
  rintro _ ⟨x, _, rfl⟩
  exact x.2

/-- A partial map preserves generic points of components when the image of
the generic points of its domain is exactly the set of generic points of its
target. -/
def MapsGenericPoints (f : X.PartialMap Y) : Prop :=
  f.hom.base '' genericPoints f.domain = genericPoints Y

/-- The generic-point-preserving condition on a partial map is exact equality
of the corresponding generic-point image and target. -/
theorem mapsGenericPoints_iff (f : X.PartialMap Y) :
    f.MapsGenericPoints ↔
      f.hom.base '' genericPoints f.domain = genericPoints Y := Iff.rfl

private theorem mapsGenericPoints_restrict_iff
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (f : X.PartialMap Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    (f.restrict U hU hU').MapsGenericPoints ↔ f.MapsGenericPoints := by
  have h := genericPoints_image_homOfLE hU f.dense_domain hU'
  change (X.homOfLE hU' ≫ f.hom).base '' genericPoints U = genericPoints Y ↔ _
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, h]
  rfl

/-- Equivalent partial maps from a scheme with finite irreducible components
on quasi-compact opens preserve generic points simultaneously. -/
theorem mapsGenericPoints_iff_of_equiv
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    {f g : X.PartialMap Y} (h : f.equiv g) :
    f.MapsGenericPoints ↔ g.MapsGenericPoints := by
  obtain ⟨U, hU, hUf, hUg, e⟩ := h
  rw [← mapsGenericPoints_restrict_iff f U hU hUf,
    ← mapsGenericPoints_restrict_iff g U hU hUg]
  exact congrArg (fun k : U.toScheme ⟶ Y ↦ k.base '' genericPoints U = genericPoints Y) e
    |>.to_iff

/-- The inverse image of the domain of a second partial map is dense in the
source whenever the first partial map preserves generic points. -/
theorem dense_compDomain_of_mapsGenericPoints
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (f : X.PartialMap Y) (g : Y.PartialMap Z)
    (hf : f.MapsGenericPoints) :
    Dense ((f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ g.domain) : X.Opens) : Set X) := by
  have hdense : Dense (genericPoints X) := by
    rw [dense_iff_closure_eq, genericPoints.closure]
  apply hdense.mono
  intro x hx
  obtain ⟨y, hy, rfl⟩ :=
    (Opens.genericPointsInAmbient_eq_of_dense f.domain f.dense_domain).symm ▸ hx
  exact ⟨y, genericPoints_subset_dense_open g.domain g.dense_domain
    (hf ▸ Set.mem_image_of_mem f.hom.base hy), rfl⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The identity partial map preserves the generic points of components. -/
theorem mapsGenericPoints_id (X : Scheme.{u})
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (PartialMap.id X).MapsGenericPoints := by
  change (X.topIso.hom ≫ 𝟙 X).base '' genericPoints (⊤ : X.Opens) = genericPoints X
  rw [Category.comp_id]
  convert Opens.genericPointsInAmbient_eq_of_dense (⊤ : X.Opens) dense_univ using 1
  rfl

/-- Composition of generic-point-preserving partial maps, defined on the
ambient image of the inverse image of the second map's domain. -/
noncomputable def compOfMapsGenericPoints
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (f : X.PartialMap Y) (g : Y.PartialMap Z)
    (hf : f.MapsGenericPoints) : X.PartialMap Z where
  domain := f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ g.domain)
  dense_domain := dense_compDomain_of_mapsGenericPoints f g hf
  hom := (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫
    f.hom ∣_ g.domain ≫ g.hom

private theorem exists_compOfMapsGenericPoints_lift
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (f : X.PartialMap Y) (g : Y.PartialMap Z) (hf : f.MapsGenericPoints)
    {T : Scheme.{u}} (i : T ⟶ f.domain) (j : T ⟶ g.domain)
    (e : j ≫ g.domain.ι = i ≫ f.hom) :
    ∃ k : T ⟶ (compOfMapsGenericPoints f g hf).domain,
      k ≫ (compOfMapsGenericPoints f g hf).domain.ι = i ≫ f.domain.ι ∧
      k ≫ (compOfMapsGenericPoints f g hf).hom = j ≫ g.hom := by
  let a := (isPullback_morphismRestrict f.hom g.domain).lift j i e
  refine ⟨a ≫ (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).hom, ?_, ?_⟩
  · change (a ≫ (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).hom) ≫
        (f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ g.domain)).ι = i ≫ f.domain.ι
    simp [a, Category.assoc]
  · change (a ≫ (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).hom) ≫
        (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫
        f.hom ∣_ g.domain ≫ g.hom = j ≫ g.hom
    simp [a, Category.assoc]

private theorem compOfMapsGenericPoints_eq_on
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (f : X.PartialMap Y) (g : Y.PartialMap Z) (hf : f.MapsGenericPoints)
    (T : X.Opens) (i : T.toScheme ⟶ f.domain) (j : T.toScheme ⟶ g.domain)
    (hi : i ≫ f.domain.ι = T.ι) (e : j ≫ g.domain.ι = i ≫ f.hom) :
    ∃ hT : T ≤ (compOfMapsGenericPoints f g hf).domain,
      X.homOfLE hT ≫ (compOfMapsGenericPoints f g hf).hom = j ≫ g.hom := by
  obtain ⟨k, hk, hk'⟩ := exists_compOfMapsGenericPoints_lift f g hf i j e
  have hT : T ≤ (compOfMapsGenericPoints f g hf).domain := by
    intro x hx
    have h := congr($(hk.trans hi) (⟨x, hx⟩ : T))
    simp only [Scheme.Hom.comp_apply, Opens.ι_apply] at h
    exact h ▸ (k (⟨x, hx⟩ : T)).2
  have he : k = X.homOfLE hT := by
    apply (cancel_mono (compOfMapsGenericPoints f g hf).domain.ι).mp
    rw [hk, hi, X.homOfLE_ι]
  exact ⟨hT, he ▸ hk'⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Composition of partial maps preserving generic points again preserves
generic points. -/
theorem mapsGenericPoints_compOfMapsGenericPoints
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (f : X.PartialMap Y) (g : Y.PartialMap Z)
    (hf : f.MapsGenericPoints) (hg : g.MapsGenericPoints) :
    (compOfMapsGenericPoints f g hf).MapsGenericPoints := by
  let U := f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ g.domain)
  let k : U.toScheme ⟶ g.domain :=
    (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫ f.hom ∣_ g.domain
  have hk : k ≫ g.domain.ι =
      X.homOfLE (f.domain.ι_image_le (f.hom ⁻¹ᵁ g.domain)) ≫ f.hom := by
    simp [k]
  have hpoints : k.base '' genericPoints U = genericPoints g.domain := by
    apply (inferInstance : IsOpenImmersion g.domain.ι).base_open.injective.image_injective
    calc
      g.domain.ι.base '' (k.base '' genericPoints U) =
          (k ≫ g.domain.ι).base '' genericPoints U := by
        simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]
      _ = genericPoints Y := by
        rw [hk, Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp,
          genericPoints_image_homOfLE
            (dense_compDomain_of_mapsGenericPoints f g hf) f.dense_domain]
        exact hf
      _ = g.domain.ι.base '' genericPoints g.domain :=
        (Opens.genericPointsInAmbient_eq_of_dense g.domain g.dense_domain).symm
  change ((f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫
    f.hom ∣_ g.domain ≫ g.hom).base '' genericPoints U = genericPoints Z
  rw [← Category.assoc]
  change (k ≫ g.hom).base '' genericPoints U = genericPoints Z
  calc
    _ = g.hom.base '' (k.base '' genericPoints U) := by
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]
    _ = genericPoints Z := by rw [hpoints]; exact hg

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Composition of generic-point-preserving partial maps respects equivalence
in both arguments. -/
theorem compOfMapsGenericPoints_equiv
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    {f₁ f₂ : X.PartialMap Y} {g₁ g₂ : Y.PartialMap Z}
    (hf₁ : f₁.MapsGenericPoints) (hf₂ : f₂.MapsGenericPoints)
    (hfg : f₁.equiv f₂) (hg : g₁.equiv g₂) :
    (compOfMapsGenericPoints f₁ g₁ hf₁).equiv
      (compOfMapsGenericPoints f₂ g₂ hf₂) := by
  obtain ⟨U, hU, hUf₁, hUf₂, ef⟩ := hfg
  obtain ⟨V, hV, hVg₁, hVg₂, eg⟩ := hg
  let f' := f₁.restrict U hU hUf₁
  let g' := g₁.restrict V hV hVg₁
  have hf' : f'.MapsGenericPoints :=
    (mapsGenericPoints_restrict_iff f₁ U hU hUf₁).mpr hf₁
  let c := compOfMapsGenericPoints f' g' hf'
  let p : c.domain.toScheme ⟶ U := X.homOfLE (U.ι_image_le (f'.hom ⁻¹ᵁ V))
  let q : c.domain.toScheme ⟶ V :=
    (U.ι.isoImage (f'.hom ⁻¹ᵁ V)).inv ≫ f'.hom ∣_ V
  have hq : q ≫ V.ι = p ≫ f'.hom := by
    simp [q, p]
  obtain ⟨h₁, e₁⟩ := compOfMapsGenericPoints_eq_on f₁ g₁ hf₁ c.domain
    (p ≫ X.homOfLE hUf₁) (q ≫ Y.homOfLE hVg₁)
    (by simp [p]) (by simpa [f', Category.assoc] using hq)
  have hq₂ : q ≫ V.ι = p ≫ X.homOfLE hUf₂ ≫ f₂.hom := by
    change q ≫ V.ι = p ≫ (f₂.restrict U hU hUf₂).hom
    rw [← ef]
    exact hq
  obtain ⟨h₂, e₂⟩ := compOfMapsGenericPoints_eq_on f₂ g₂ hf₂ c.domain
    (p ≫ X.homOfLE hUf₂) (q ≫ Y.homOfLE hVg₂)
    (by simp [p]) (by simpa [Category.assoc] using hq₂)
  refine ⟨c.domain, c.dense_domain, h₁, h₂, ?_⟩
  change X.homOfLE h₁ ≫ _ = X.homOfLE h₂ ≫ _
  rw [e₁, e₂]
  simpa only [restrict_hom, Category.assoc] using congrArg (fun k ↦ q ≫ k) eg

/-- Composing the identity partial map on the source with a partial map is
equivalent to that partial map. -/
theorem id_compOfMapsGenericPoints
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (f : X.PartialMap Y) :
    (compOfMapsGenericPoints (PartialMap.id X) f
      (mapsGenericPoints_id X)).equiv f := by
  obtain ⟨hT, e⟩ := compOfMapsGenericPoints_eq_on (PartialMap.id X) f
    (mapsGenericPoints_id X) f.domain (f.domain.ι ≫ X.topIso.inv) (𝟙 _)
    (by simp [PartialMap.id, Scheme.Hom.toPartialMap])
    (by simp [PartialMap.id, Scheme.Hom.toPartialMap])
  refine ⟨f.domain, f.dense_domain, hT, le_rfl, ?_⟩
  simpa [restrict] using e

/-- Composing a generic-point-preserving partial map with the identity on its
target is equivalent to the original partial map. -/
theorem compOfMapsGenericPoints_id
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (f : X.PartialMap Y) (hf : f.MapsGenericPoints) :
    (compOfMapsGenericPoints f (PartialMap.id Y) hf).equiv f := by
  obtain ⟨hT, e⟩ := compOfMapsGenericPoints_eq_on f (PartialMap.id Y) hf
    f.domain (𝟙 _) (f.hom ≫ Y.topIso.inv) (by simp)
    (by simp [PartialMap.id, Scheme.Hom.toPartialMap])
  refine ⟨f.domain, f.dense_domain, hT, le_rfl, ?_⟩
  simpa [restrict, PartialMap.id, Scheme.Hom.toPartialMap] using e

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Composition of generic-point-preserving partial maps is associative up to
partial-map equivalence. -/
theorem compOfMapsGenericPoints_assoc
    [HasFiniteIrreducibleComponentsOnCompactOpens W]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (f : W.PartialMap X) (g : X.PartialMap Y) (h : Y.PartialMap Z)
    (hf : f.MapsGenericPoints) (hg : g.MapsGenericPoints) :
    (compOfMapsGenericPoints
      (compOfMapsGenericPoints f g hf) h
      (mapsGenericPoints_compOfMapsGenericPoints f g hf hg)).equiv
        (compOfMapsGenericPoints f
          (compOfMapsGenericPoints g h hg) hf) := by
  let fg := compOfMapsGenericPoints f g hf
  let gh := compOfMapsGenericPoints g h hg
  let l := compOfMapsGenericPoints fg h (mapsGenericPoints_compOfMapsGenericPoints f g hf hg)
  let r := compOfMapsGenericPoints f gh hf
  change l.equiv r
  let p : l.domain.toScheme ⟶ fg.domain :=
    W.homOfLE (fg.domain.ι_image_le (fg.hom ⁻¹ᵁ h.domain))
  let q : l.domain.toScheme ⟶ h.domain :=
    (fg.domain.ι.isoImage (fg.hom ⁻¹ᵁ h.domain)).inv ≫ fg.hom ∣_ h.domain
  let i : l.domain.toScheme ⟶ f.domain :=
    p ≫ W.homOfLE (f.domain.ι_image_le (f.hom ⁻¹ᵁ g.domain))
  let j : l.domain.toScheme ⟶ g.domain :=
    p ≫ (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫ f.hom ∣_ g.domain
  have hq : q ≫ h.domain.ι = p ≫ fg.hom := by
    simp [q, p]
  have hj : j ≫ g.domain.ι = i ≫ f.hom := by
    simp [j, i, Category.assoc]
  have hfg : p ≫ fg.hom = j ≫ g.hom := by
    simp [j, fg, compOfMapsGenericPoints, Category.assoc]
  have hl : l.hom = q ≫ h.hom := by
    simp [l, q, compOfMapsGenericPoints, Category.assoc]
  obtain ⟨k, hk₁, hk₂⟩ :=
    exists_compOfMapsGenericPoints_lift g h hg j q (hq.trans hfg)
  obtain ⟨hT, e⟩ := compOfMapsGenericPoints_eq_on f gh hf l.domain i k
    (by simp [i, p]) (hk₁.trans hj)
  refine ⟨l.domain, l.dense_domain, le_rfl, hT, ?_⟩
  simpa only [restrict_hom, homOfLE_rfl, Category.id_comp] using
    hl.trans (e.trans hk₂).symm

end PartialMap

namespace RationalMap

/-- A rational map preserves generic points of components when one of its
partial-map representatives does so. -/
def MapsGenericPoints (f : X ⤏ Y) : Prop :=
  ∃ g : X.PartialMap Y, g.MapsGenericPoints ∧ g.toRationalMap = f

/-- A rational map preserves generic points exactly when it has a
generic-point-preserving partial-map representative. -/
theorem mapsGenericPoints_iff_exists_partialMap (f : X ⤏ Y) :
    f.MapsGenericPoints ↔
      ∃ g : X.PartialMap Y, g.MapsGenericPoints ∧ g.toRationalMap = f := Iff.rfl

/-- For a source with finite irreducible components on quasi-compact opens, a
rational map preserves generic points exactly when its canonical
representative does. -/
theorem mapsGenericPoints_iff_representative
    [HasFiniteIrreducibleComponentsOnCompactOpens X] (f : X ⤏ Y) :
    f.MapsGenericPoints ↔ f.representative.MapsGenericPoints := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (PartialMap.mapsGenericPoints_iff_of_equiv
      g.representative_toRationalMap_equiv).mpr hg
  · intro hf
    exact ⟨f.representative, hf, f.toRationalMap_representative⟩

/-- The identity rational map preserves the generic points of components. -/
theorem mapsGenericPoints_id (X : Scheme.{u})
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (RationalMap.id X).MapsGenericPoints :=
  ⟨PartialMap.id X, PartialMap.mapsGenericPoints_id X, rfl⟩

/-- Composition of rational maps preserving generic points, obtained from the
canonical representatives and explicit partial-map composition. -/
noncomputable def compOfMapsGenericPoints
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (f : X ⤏ Y) (g : Y ⤏ Z) (hf : f.MapsGenericPoints) : X ⤏ Z :=
  (PartialMap.compOfMapsGenericPoints f.representative g.representative
    ((mapsGenericPoints_iff_representative f).mp hf)).toRationalMap

/-- Composition of rational maps preserving generic points again preserves
generic points. -/
theorem mapsGenericPoints_compOfMapsGenericPoints
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (f : X ⤏ Y) (g : Y ⤏ Z)
    (hf : f.MapsGenericPoints) (hg : g.MapsGenericPoints) :
    (compOfMapsGenericPoints f g hf).MapsGenericPoints := by
  refine ⟨_, PartialMap.mapsGenericPoints_compOfMapsGenericPoints
    f.representative g.representative
    ((mapsGenericPoints_iff_representative f).mp hf)
    ((mapsGenericPoints_iff_representative g).mp hg), rfl⟩

private theorem compOfMapsGenericPoints_toRationalMap
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (f : X.PartialMap Y) (g : Y.PartialMap Z) (hf : f.MapsGenericPoints) :
    compOfMapsGenericPoints f.toRationalMap g.toRationalMap ⟨f, hf, rfl⟩ =
      (PartialMap.compOfMapsGenericPoints f g hf).toRationalMap := by
  apply PartialMap.toRationalMap_eq_iff.mpr
  exact PartialMap.compOfMapsGenericPoints_equiv _ hf
    f.representative_toRationalMap_equiv g.representative_toRationalMap_equiv

end RationalMap

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Schemes whose quasi-compact open subschemes have finitely many
irreducible components. -/
def FiniteComponentRationalMapCat :=
  { X : Scheme.{u} // Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X }

namespace FiniteComponentRationalMapCat

/-- An object of the finite-component rational-map category carries the
canonical finiteness instance on its underlying scheme. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpens
    (X : FiniteComponentRationalMapCat.{u}) :
    Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X.1 :=
  X.2

/-- A morphism between finite-component schemes is a rational map preserving
the generic points of components. -/
def Hom (X Y : FiniteComponentRationalMapCat.{u}) :=
  { f : X.1 ⤏ Y.1 // f.MapsGenericPoints }

namespace Hom

/-- The identity morphism of a finite-component scheme. -/
def id (X : FiniteComponentRationalMapCat.{u}) : Hom X X :=
  ⟨Scheme.RationalMap.id X.1, Scheme.RationalMap.mapsGenericPoints_id X.1⟩

/-- Composition of morphisms between finite-component schemes. -/
noncomputable def comp {X Y Z : FiniteComponentRationalMapCat.{u}}
    (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  ⟨Scheme.RationalMap.compOfMapsGenericPoints f.1 g.1 f.2,
    Scheme.RationalMap.mapsGenericPoints_compOfMapsGenericPoints
      f.1 g.1 f.2 g.2⟩

/-- The identity morphism on the source is a left identity for composition. -/
theorem id_comp {X Y : FiniteComponentRationalMapCat.{u}} (f : Hom X Y) :
    comp (id X) f = f := by
  apply Subtype.ext
  change Scheme.RationalMap.compOfMapsGenericPoints (Scheme.RationalMap.id X.1) f.1
    (Scheme.RationalMap.mapsGenericPoints_id X.1) = f.1
  have e := Scheme.RationalMap.compOfMapsGenericPoints_toRationalMap
    (Scheme.PartialMap.id X.1) f.1.representative (Scheme.PartialMap.mapsGenericPoints_id X.1)
  have e' := Scheme.PartialMap.toRationalMap_eq_iff.mpr
    (Scheme.PartialMap.id_compOfMapsGenericPoints f.1.representative)
  simpa only [Scheme.RationalMap.toRationalMap_representative] using e.trans e'

/-- The identity morphism on the target is a right identity for composition. -/
theorem comp_id {X Y : FiniteComponentRationalMapCat.{u}} (f : Hom X Y) :
    comp f (id Y) = f := by
  apply Subtype.ext
  change Scheme.RationalMap.compOfMapsGenericPoints f.1 (Scheme.RationalMap.id Y.1) f.2 = f.1
  have hf := (Scheme.RationalMap.mapsGenericPoints_iff_representative f.1).mp f.2
  have e := Scheme.RationalMap.compOfMapsGenericPoints_toRationalMap
    f.1.representative (Scheme.PartialMap.id Y.1) hf
  have e' := Scheme.PartialMap.toRationalMap_eq_iff.mpr
    (Scheme.PartialMap.compOfMapsGenericPoints_id f.1.representative hf)
  simpa only [Scheme.RationalMap.toRationalMap_representative] using e.trans e'

/-- Composition of finite-component rational maps is associative. -/
theorem comp_assoc {W X Y Z : FiniteComponentRationalMapCat.{u}}
    (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    comp (comp f g) h = comp f (comp g h) := by
  apply Subtype.ext
  change Scheme.RationalMap.compOfMapsGenericPoints
      (Scheme.RationalMap.compOfMapsGenericPoints f.1 g.1 f.2) h.1
      (Scheme.RationalMap.mapsGenericPoints_compOfMapsGenericPoints f.1 g.1 f.2 g.2) =
    Scheme.RationalMap.compOfMapsGenericPoints f.1
      (Scheme.RationalMap.compOfMapsGenericPoints g.1 h.1 g.2) f.2
  let f' := f.1.representative
  let g' := g.1.representative
  let h' := h.1.representative
  have hf : f'.MapsGenericPoints :=
    (Scheme.RationalMap.mapsGenericPoints_iff_representative f.1).mp f.2
  have hg : g'.MapsGenericPoints :=
    (Scheme.RationalMap.mapsGenericPoints_iff_representative g.1).mp g.2
  have hfg := Scheme.PartialMap.mapsGenericPoints_compOfMapsGenericPoints f' g' hf hg
  have efg := Scheme.RationalMap.compOfMapsGenericPoints_toRationalMap f' g' hf
  have egh := Scheme.RationalMap.compOfMapsGenericPoints_toRationalMap g' h' hg
  have el := Scheme.RationalMap.compOfMapsGenericPoints_toRationalMap
    (Scheme.PartialMap.compOfMapsGenericPoints f' g' hf) h' hfg
  have er := Scheme.RationalMap.compOfMapsGenericPoints_toRationalMap
    f' (Scheme.PartialMap.compOfMapsGenericPoints g' h' hg) hf
  calc
    _ = (Scheme.PartialMap.compOfMapsGenericPoints
          (Scheme.PartialMap.compOfMapsGenericPoints f' g' hf) h' hfg).toRationalMap := by
      simpa only [← efg, f', g', h', Scheme.RationalMap.toRationalMap_representative] using el
    _ = (Scheme.PartialMap.compOfMapsGenericPoints f'
          (Scheme.PartialMap.compOfMapsGenericPoints g' h' hg) hf).toRationalMap :=
      Scheme.PartialMap.toRationalMap_eq_iff.mpr
        (Scheme.PartialMap.compOfMapsGenericPoints_assoc f' g' h' hf hg)
    _ = _ := by
      symm
      simpa only [← egh, f', g', h', Scheme.RationalMap.toRationalMap_representative] using er

end Hom

/-- The category of finite-component schemes and rational maps preserving
generic points of components. -/
noncomputable instance instCategory :
    CategoryTheory.Category.{u} FiniteComponentRationalMapCat.{u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

end FiniteComponentRationalMapCat

end AlgebraicGeometry
