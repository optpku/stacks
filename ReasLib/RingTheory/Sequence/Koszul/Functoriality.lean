/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Bimod.ChangeOfScalars
public import ReasLib.RingTheory.Sequence.Koszul.Map
public import ReasLib.RingTheory.Sequence.Koszul.Monoid
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of module-valued Koszul algebras

A linear map intertwining two linear forms induces a morphism of their commutative Koszul
algebras. The target Koszul algebra may then be restricted to a canonical bimodule over the
source algebra; its left action is multiplication after applying the Koszul map.

@stack 0624
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace KoszulComplex

variable {R E E' E'' : Type u} [CommRing R]
variable [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E']
variable [AddCommGroup E''] [Module R E'']
variable {phi : E →ₗ[R] R} {phi' : E' →ₗ[R] R} {phi'' : E'' →ₗ[R] R}

/-- A compatible Koszul chain map preserves the exterior unit. -/
theorem map_one (psi : E →ₗ[R] E') (hpsi : phi'.comp psi = phi) :
    oneHom phi ≫ map psi hpsi = oneHom phi' := sorry

/-- A compatible Koszul chain map preserves exterior multiplication. -/
theorem map_mul (psi : E →ₗ[R] E') (hpsi : phi'.comp psi = phi) :
    mulHom phi ≫ map psi hpsi =
      (map psi hpsi ⊗ₘ map psi hpsi) ≫ mulHom phi' := sorry

/-- The commutative-monoid morphism induced by a compatible map of linear forms. -/
@[stacks 0624 "Lemma 15.28.3", stacks 062K "functoriality map of module-valued Koszul algebras",
  stacks 0GZJ "multiplicative map of powered Koszul algebras"]
noncomputable def commMonMap (psi : E →ₗ[R] E') (hpsi : phi'.comp psi = phi) :
    commMon phi ⟶ commMon phi' :=
  CommMon.homMk (Mon.Hom.mk' (map psi hpsi) (map_one psi hpsi) (map_mul psi hpsi))

/-- Forgetting multiplication from a Koszul-algebra map recovers its Koszul chain map. -/
@[simp]
theorem commMonMap_hom (psi : E →ₗ[R] E') (hpsi : phi'.comp psi = phi) :
    (commMonMap psi hpsi).hom.hom = map psi hpsi := sorry

/-- In degree `n`, a Koszul-algebra map is the corresponding exterior-power map. -/
@[simp]
theorem commMonMap_hom_f (psi : E →ₗ[R] E') (hpsi : phi'.comp psi = phi)
    (n : ℕ) :
    (commMonMap psi hpsi).hom.hom.f n = mapComponent psi n := sorry

/-- The Koszul-algebra map induced by the identity linear map is the identity. -/
@[simp]
theorem commMonMap_id (phi : E →ₗ[R] R) :
    commMonMap (phi := phi) (phi' := phi) LinearMap.id (LinearMap.comp_id phi) =
      𝟙 (commMon phi) := sorry

/-- Koszul-algebra maps induced by compatible linear maps preserve composition. -/
theorem commMonMap_comp (psi : E →ₗ[R] E') (chi : E' →ₗ[R] E'')
    (hpsi : phi'.comp psi = phi) (hchi : phi''.comp chi = phi') :
    commMonMap (chi.comp psi) (comp_compatible psi chi hpsi hchi) =
      commMonMap psi hpsi ≫ commMonMap chi hchi := sorry

/-- Multiplication after a compatible Koszul map is the left action of the source algebra on
the target algebra. -/
@[stacks 0GZJ "left action induced by a powered Koszul transition"]
noncomputable def leftAction (psi : E →ₗ[R] E') (hpsi : phi'.comp psi = phi) :
    HomologicalComplex.tensorObj (koszulComplex phi) (koszulComplex phi') ⟶
      koszulComplex phi' :=
  (map psi hpsi ⊗ₘ 𝟙 (koszulComplex phi')) ≫ mulHom phi'

/-- The target Koszul algebra as the canonical right-extension bimodule for
`commMonMap psi hpsi`; equivalently, its left regular action is restricted to the source. -/
@[stacks 0GZJ "restriction bimodule of a powered Koszul transition"]
noncomputable def restrictionBimodule (psi : E →ₗ[R] E')
    (hpsi : phi'.comp psi = phi) :
    Bimod (commMon phi).toMon (commMon phi').toMon :=
  (commMonMap psi hpsi).hom.rightExtensionBimod

/-- Restriction of the left regular action does not change the target Koszul complex. -/
@[simp]
theorem restrictionBimodule_X (psi : E →ₗ[R] E')
    (hpsi : phi'.comp psi = phi) :
    (restrictionBimodule psi hpsi).X = koszulComplex phi' := sorry

/-- The left action of the restriction bimodule is the explicit multiplication-after-map
chain morphism. -/
@[simp]
theorem restrictionBimodule_actLeft (psi : E →ₗ[R] E')
    (hpsi : phi'.comp psi = phi) :
    (restrictionBimodule psi hpsi).actLeft = leftAction psi hpsi := sorry

end KoszulComplex
