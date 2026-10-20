/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.CommRingCat
public import Mathlib.Topology.Sheaves.Sheafify
public import ReasLib.Algebra.Category.Ring.Sheaf.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of localization presheaves

Objectwise localization of a commutative-ring presheaf commutes with taking stalks.  This file
owns the genuinely topological part of the localization API: the submonoid of germs and the
localization statements before and after sheafification.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace TopCat.Presheaf.SectionLocalization

variable {X : TopCat.{u}} {O : X.Presheaf CommRingCat.{u}}
variable (S : CategoryTheory.Presheaf.SubmonoidPresheaf O)

/-- Regard mathlib's topological-space-specific submonoid presheaf as the general
category-indexed submonoid presheaf used by the site-level localization API. -/
def ofTopCat (T : TopCat.Presheaf.SubmonoidPresheaf O) :
    CategoryTheory.Presheaf.SubmonoidPresheaf O :=
  CategoryTheory.Presheaf.SubmonoidPresheaf.mk T.obj
    (fun {U V} f ↦ T.map (U := U) (V := V) f)

/-- Specialize a category-indexed submonoid presheaf on open sets to mathlib's
topological-space-specific representation. -/
def toTopCat (S : CategoryTheory.Presheaf.SubmonoidPresheaf O) :
    TopCat.Presheaf.SubmonoidPresheaf O where
  obj := S.obj
  map := fun {U V} f ↦ S.map (U := U) (V := V) f

/-- Generalizing and then specializing a topological submonoid presheaf returns the
original family. -/
theorem toTopCat_ofTopCat (T : TopCat.Presheaf.SubmonoidPresheaf O) :
    toTopCat (ofTopCat T) = T := rfl

/-- Specializing and then generalizing a site-level submonoid presheaf on open sets
returns the original family. -/
theorem ofTopCat_toTopCat :
    ofTopCat (toTopCat S) = S := rfl

/-- The submonoid of the stalk represented by germs of sections belonging to the compatible
submonoid family. -/
@[stacks 01D0 "submonoid of germs"]
def stalkSubmonoid (x : X) : Submonoid (O.stalk x) where
  carrier :=
    { z | ∃ (U : Opens X) (hx : x ∈ U) (s : S.obj (op U)),
        (O.germ U x hx).hom s.1 = z }
  one_mem' := by
    refine ⟨⊤, by simp, 1, ?_⟩
    simp
  mul_mem' := by
    rintro z w ⟨U, hxU, s, rfl⟩ ⟨V, hxV, t, rfl⟩
    let W : Opens X := U ⊓ V
    have hxW : x ∈ W := ⟨hxU, hxV⟩
    let sW : S.obj (op W) :=
      ⟨O.map (homOfLE (show W ≤ U from inf_le_left)).op s.1,
        S.map (homOfLE (show W ≤ U from inf_le_left)).op s.2⟩
    let tW : S.obj (op W) :=
      ⟨O.map (homOfLE (show W ≤ V from inf_le_right)).op t.1,
        S.map (homOfLE (show W ≤ V from inf_le_right)).op t.2⟩
    refine ⟨W, hxW, sW * tW, ?_⟩
    change O.germ W x hxW (sW.1 * tW.1) =
      O.germ U x hxU s.1 * O.germ V x hxV t.1
    rw [map_mul, O.germ_res_apply, O.germ_res_apply]

/-- The stalk of the objectwise localization is naturally an algebra over the original
stalk through the stalk of the canonical localization map. -/
noncomputable instance stalkAlgebra (x : X) :
    Algebra (O.stalk x) ((stalkFunctor CommRingCat x).obj S.localizationPresheaf) :=
  RingHom.toAlgebra (((stalkFunctor CommRingCat x).map S.toLocalizationPresheaf).hom)

/-- The stalk of an objectwise localization presheaf is the localization at the submonoid of
distinguished germs. -/
@[stacks 01D0 "stalk of a localization presheaf"]
theorem stalkIsLocalization (x : X) :
    IsLocalization (stalkSubmonoid S x)
      ((stalkFunctor CommRingCat x).obj S.localizationPresheaf) := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨z, U, hxU, s, rfl⟩
    change IsUnit
      (((stalkFunctor CommRingCat x).map S.toLocalizationPresheaf).hom
        ((O.germ U x hxU).hom s.1))
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    exact (IsLocalization.map_units (S.localizationPresheaf.obj (op U)) s).map
      (TopCat.Presheaf.germ S.localizationPresheaf U x hxU).hom
  · intro z
    obtain ⟨U, hxU, zU, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq
        (S.localizationPresheaf : X.Presheaf CommRingCat) z
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (S.obj (op U)) zU
    refine ⟨⟨(O.germ U x hxU).hom a,
      ⟨(O.germ U x hxU).hom s.1, U, hxU, s, rfl⟩⟩, ?_⟩
    dsimp only
    let gL : S.localizationPresheaf.obj (op U) →+*
        ((stalkFunctor CommRingCat x).obj S.localizationPresheaf) :=
      (TopCat.Presheaf.germ S.localizationPresheaf U x hxU).hom
    change gL zU *
        (((stalkFunctor CommRingCat x).map S.toLocalizationPresheaf).hom
          ((O.germ U x hxU).hom s.1)) =
      ((stalkFunctor CommRingCat x).map S.toLocalizationPresheaf).hom
        ((O.germ U x hxU).hom a)
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change gL zU * gL (algebraMap (O.obj (op U))
        (S.localizationPresheaf.obj (op U)) s.1) =
      gL (algebraMap (O.obj (op U)) (S.localizationPresheaf.obj (op U)) a)
    rw [← map_mul, hs]
  · intro a b hab
    obtain ⟨U, hxU, aU, rfl⟩ := O.exists_germ_eq a
    obtain ⟨V, hxV, bV, rfl⟩ := O.exists_germ_eq b
    change ((stalkFunctor CommRingCat x).map S.toLocalizationPresheaf).hom
        ((O.germ U x hxU).hom aU) =
      ((stalkFunctor CommRingCat x).map S.toLocalizationPresheaf).hom
        ((O.germ V x hxV).hom bV) at hab
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply] at hab
    obtain ⟨W, hxW, iWU, iWV, hW⟩ :=
      TopCat.Presheaf.germ_eq
        (S.localizationPresheaf : X.Presheaf CommRingCat) x hxU hxV _ _ hab
    change S.localizationMap iWU.op (algebraMap (O.obj (op U))
        (S.localizationPresheaf.obj (op U)) aU) =
      S.localizationMap iWV.op (algebraMap (O.obj (op V))
        (S.localizationPresheaf.obj (op V)) bV) at hW
    change IsLocalization.map (Localization (S.obj (op W))) (O.map iWU.op).hom
        (S.map iWU.op) (algebraMap (O.obj (op U))
          (S.localizationPresheaf.obj (op U)) aU) =
      IsLocalization.map (Localization (S.obj (op W))) (O.map iWV.op).hom
        (S.map iWV.op) (algebraMap (O.obj (op V))
          (S.localizationPresheaf.obj (op V)) bV) at hW
    rw [IsLocalization.map_eq, IsLocalization.map_eq] at hW
    obtain ⟨c, hc⟩ :=
      IsLocalization.exists_of_eq (M := S.obj (op W)) hW
    refine ⟨⟨(O.germ W x hxW).hom c.1, W, hxW, c, rfl⟩, ?_⟩
    dsimp only
    let gW : O.obj (op W) →+* O.stalk x := (O.germ W x hxW).hom
    change gW c.1 * (O.germ U x hxU).hom aU =
      gW c.1 * (O.germ V x hxV).hom bV
    calc
      _ = gW c.1 * gW ((O.map iWU.op).hom aU) := by
        rw [O.germ_res_apply iWU x hxW aU]
      _ = gW (c.1 * (O.map iWU.op).hom aU) := (map_mul gW _ _).symm
      _ = gW (c.1 * (O.map iWV.op).hom bV) := congrArg gW hc
      _ = gW c.1 * gW ((O.map iWV.op).hom bV) := map_mul gW _ _
      _ = _ := by rw [O.germ_res_apply iWV x hxW bV]

/-- The stalk of the sheafified localization is naturally an algebra over the original
presheaf stalk through the canonical map to the sheafified localization. -/
noncomputable instance sheafifiedStalkAlgebra (x : X) :
    Algebra (O.stalk x)
      ((stalkFunctor CommRingCat x).obj
        (S.localizationSheaf (J := Opens.grothendieckTopology X)).obj) :=
  RingHom.toAlgebra
    (((stalkFunctor CommRingCat x).map
      (S.toSheafifiedLocalization (J := Opens.grothendieckTopology X))).hom)

/-- Sheafification does not change the localized stalk; it is still the localization at the
submonoid of distinguished germs. -/
@[stacks 01D0 "stalk after sheafified localization"]
theorem sheafifiedStalkIsLocalization (x : X) :
    IsLocalization (stalkSubmonoid S x)
      ((stalkFunctor CommRingCat x).obj
        (S.localizationSheaf (J := Opens.grothendieckTopology X)).obj) := by
  let unit := (stalkFunctor CommRingCat x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      S.localizationPresheaf)
  -- Local instance justification (proof-local temporary data): this is the temporary stalk-unit
  -- isomorphism used by `asIso` below.
  letI : IsIso unit := by
    dsimp only [unit]
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
      x CommRingCat S.localizationPresheaf
  let e := asIso unit
  let eAlg : ((stalkFunctor CommRingCat x).obj S.localizationPresheaf) ≃ₐ[O.stalk x]
      ((stalkFunctor CommRingCat x).obj
        (S.localizationSheaf (J := Opens.grothendieckTopology X)).obj) :=
    { e.commRingCatIsoToRingEquiv with
      commutes' := fun r ↦ by
        have hnat : S.toLocalizationPresheaf ≫
              CategoryTheory.toSheafify (Opens.grothendieckTopology X)
                S.localizationPresheaf =
            S.toSheafifiedLocalization
              (J := Opens.grothendieckTopology X) := by
          rw [CategoryTheory.toSheafify_naturality]
          rfl
        change e.hom.hom
            (((stalkFunctor CommRingCat x).map S.toLocalizationPresheaf).hom r) =
          ((stalkFunctor CommRingCat x).map
            (S.toSheafifiedLocalization
              (J := Opens.grothendieckTopology X))).hom r
        simp only [e, asIso_hom, unit]
        rw [← ConcreteCategory.comp_apply]
        rw [← Functor.map_comp]
        exact congrArg
          (fun f ↦ ((stalkFunctor CommRingCat x).map f).hom r) hnat }
  -- Local instance justification (proof-local temporary data): this is the proved stalk-localization
  -- fact used by `isLocalization_of_algEquiv` below.
  letI : IsLocalization (stalkSubmonoid S x)
      ((stalkFunctor CommRingCat x).obj S.localizationPresheaf) :=
    stalkIsLocalization S x
  exact IsLocalization.isLocalization_of_algEquiv (stalkSubmonoid S x) eAlg

/-- The canonical localization map equips the stalk of a topological submonoid
presheaf's objectwise localization with its algebra structure. -/
noncomputable instance stalkAlgebraOfTopCat
    (T : TopCat.Presheaf.SubmonoidPresheaf O) (x : X) :
    Algebra (O.stalk x) ((stalkFunctor CommRingCat x).obj T.localizationPresheaf) :=
  RingHom.toAlgebra (((stalkFunctor CommRingCat x).map T.toLocalizationPresheaf).hom)

/-- The stalk of a topological submonoid presheaf's objectwise localization is the
localization at the submonoid of distinguished germs. -/
theorem stalkIsLocalizationOfTopCat
    (T : TopCat.Presheaf.SubmonoidPresheaf O) (x : X) :
    IsLocalization (stalkSubmonoid (ofTopCat T) x)
      ((stalkFunctor CommRingCat x).obj T.localizationPresheaf) := by
  change IsLocalization (stalkSubmonoid (ofTopCat T) x)
    ((stalkFunctor CommRingCat x).obj (ofTopCat T).localizationPresheaf)
  exact stalkIsLocalization (ofTopCat T) x

end TopCat.Presheaf.SectionLocalization
