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
      RingHom.id (AdicCompletion (maximalIdeal B) B) := sorry

/-- The completion maps induced by an inverse ring equivalence and the original equivalence
compose to the identity. -/
theorem mapLocal_symm_comp (e : A ≃+* B) :
    (mapLocal e.symm.toRingHom).comp (mapLocal e.toRingHom) =
      RingHom.id (AdicCompletion (maximalIdeal A) A) := sorry

/-- The canonical equivalence of maximal-ideal completions induced by a local ring equivalence. -/
@[stacks 0CAR "maximal-ideal completion under a ring equivalence"]
noncomputable def mapLocalEquiv (e : A ≃+* B) :
    AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B :=
  RingEquiv.ofRingHom (mapLocal e.toRingHom) (mapLocal e.symm.toRingHom)
    (mapLocal_comp_symm e) (mapLocal_symm_comp e)

/-- The map on maximal-ideal completions induced by a ring equivalence is bijective. -/
theorem mapLocal_bijective (e : A ≃+* B) :
    Function.Bijective (mapLocal e.toRingHom) := sorry

/-- The underlying map of `mapLocalEquiv` is the canonical local completion map. -/
@[simp]
theorem mapLocalEquiv_toRingHom (e : A ≃+* B) :
    (mapLocalEquiv e).toRingHom = mapLocal e.toRingHom := sorry

/-- The completion equivalence induced by a local-ring equivalence sends a dense source element
to the dense image element. -/
@[simp]
theorem mapLocalEquiv_apply_algebraMap (e : A ≃+* B) (a : A) :
    mapLocalEquiv e (algebraMap A (AdicCompletion (maximalIdeal A) A) a) =
      algebraMap B (AdicCompletion (maximalIdeal B) B) (e a) := sorry

/-- The inverse completion equivalence sends a dense target element to the dense inverse-image
element. -/
@[simp]
theorem mapLocalEquiv_symm_apply_algebraMap (e : A ≃+* B) (b : B) :
    (mapLocalEquiv e).symm (algebraMap B (AdicCompletion (maximalIdeal B) B) b) =
      algebraMap A (AdicCompletion (maximalIdeal A) A) (e.symm b) := sorry

/-- The completion equivalence intertwines the two canonical completion maps. -/
theorem mapLocalEquiv_comp (e : A ≃+* B) :
    (mapLocalEquiv e).toRingHom.comp
        (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
      (algebraMap B (AdicCompletion (maximalIdeal B) B)).comp e.toRingHom := sorry

end AdicCompletion
