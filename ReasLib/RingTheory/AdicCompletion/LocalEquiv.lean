/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.LocalMap
public import ReasLib.RingTheory.LocalRing.Equiv

@[expose] public section

/-!
# Maximal-ideal completions under local ring equivalences

This file owns the equivalence-level functoriality of maximal-ideal completion.  The underlying
map is always `AdicCompletion.mapLocal`; no quotient-stage presentation is exposed to consumers.
-/

noncomputable section

open IsLocalRing

namespace AdicCompletion

universe u v

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]

/-- The completion maps induced by a ring equivalence and its inverse compose to the identity. -/
theorem mapLocal_comp_symm (e : A ≃+* B) :
    (mapLocal e.toRingHom).comp (mapLocal e.symm.toRingHom) =
      RingHom.id (AdicCompletion (maximalIdeal B) B) := by
  rw [mapLocal_comp_mapLocal]
  calc
    mapLocal (e.toRingHom.comp e.symm.toRingHom) = mapLocal (RingHom.id B) := by
      congr 1
      exact RingHom.ext e.apply_symm_apply
    _ = _ := mapLocal_id B

/-- The completion maps induced by an inverse ring equivalence and the original equivalence
compose to the identity. -/
theorem mapLocal_symm_comp (e : A ≃+* B) :
    (mapLocal e.symm.toRingHom).comp (mapLocal e.toRingHom) =
      RingHom.id (AdicCompletion (maximalIdeal A) A) := by
  rw [mapLocal_comp_mapLocal]
  calc
    mapLocal (e.symm.toRingHom.comp e.toRingHom) = mapLocal (RingHom.id A) := by
      congr 1
      exact RingHom.ext e.symm_apply_apply
    _ = _ := mapLocal_id A

/-- The canonical equivalence of maximal-ideal completions induced by a local ring equivalence. -/
@[stacks 0CAR "maximal-ideal completion under a ring equivalence"]
noncomputable def mapLocalEquiv (e : A ≃+* B) :
    AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B :=
  RingEquiv.ofRingHom (mapLocal e.toRingHom) (mapLocal e.symm.toRingHom)
    (mapLocal_comp_symm e) (mapLocal_symm_comp e)

/-- The map on maximal-ideal completions induced by a ring equivalence is bijective. -/
theorem mapLocal_bijective (e : A ≃+* B) :
    Function.Bijective (mapLocal e.toRingHom) :=
  (mapLocalEquiv e).bijective

/-- The underlying map of `mapLocalEquiv` is the canonical local completion map. -/
@[simp]
theorem mapLocalEquiv_toRingHom (e : A ≃+* B) :
    (mapLocalEquiv e).toRingHom = mapLocal e.toRingHom := rfl

/-- The completion equivalence induced by a local-ring equivalence sends a dense source element
to the dense image element. -/
@[simp]
theorem mapLocalEquiv_apply_algebraMap (e : A ≃+* B) (a : A) :
    mapLocalEquiv e (algebraMap A (AdicCompletion (maximalIdeal A) A) a) =
      algebraMap B (AdicCompletion (maximalIdeal B) B) (e a) :=
  mapLocal_apply_algebraMap e.toRingHom a

/-- The inverse completion equivalence sends a dense target element to the dense inverse-image
element. -/
@[simp]
theorem mapLocalEquiv_symm_apply_algebraMap (e : A ≃+* B) (b : B) :
    (mapLocalEquiv e).symm (algebraMap B (AdicCompletion (maximalIdeal B) B) b) =
      algebraMap A (AdicCompletion (maximalIdeal A) A) (e.symm b) :=
  mapLocal_apply_algebraMap e.symm.toRingHom b

/-- The completion equivalence intertwines the two canonical completion maps. -/
theorem mapLocalEquiv_comp (e : A ≃+* B) :
    (mapLocalEquiv e).toRingHom.comp
        (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
      (algebraMap B (AdicCompletion (maximalIdeal B) B)).comp e.toRingHom :=
  mapLocal_comp e.toRingHom

end AdicCompletion
