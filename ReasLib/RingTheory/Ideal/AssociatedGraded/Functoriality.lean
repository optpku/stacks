/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic

/-!
# Functoriality of associated graded objects

This leaf contains the small computation and composition API for the quotient-Rees
associated graded construction for filtered-ring arguments.
-/

@[expose] public section

universe u v w

namespace Ideal.AssociatedGraded

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S]
variable {T : Type w} [CommRing T]
variable {I : Ideal R} {J : Ideal S} {K : Ideal T}

/-- Coercion computation for the degree-`n` component of an associated graded map. -/
@[simp]
theorem mapGrade_coe
    (f : R →+* S) (hIJ : I ≤ Ideal.comap f J) (n : ℕ)
    (x : grade I n) :
    ((mapGrade I J f hIJ n x : grade J n) : ring J) = map f hIJ x := sorry

/-- The degreewise associated graded map preserves addition. -/
theorem mapGradeLinear_map_add
    (f : R →+* S) (hIJ : I ≤ Ideal.comap f J) (n : ℕ)
    (x y : grade I n) :
    mapGrade I J f hIJ n (x + y) =
      mapGrade I J f hIJ n x + mapGrade I J f hIJ n y := sorry

/-- The degreewise associated graded map respects scalar multiplication through the base-ring
homomorphism. -/
theorem mapGradeLinear_map_smul
    (f : R →+* S) (hIJ : I ≤ Ideal.comap f J) (n : ℕ)
    (r : R) (x : grade I n) :
    mapGrade I J f hIJ n (r • x) =
      f r • mapGrade I J f hIJ n x := sorry

/-- The degree-`n` associated graded map as a semilinear map over the base-ring homomorphism.

The older `mapGrade` view remains a convenient coercion-level API, while this bundled owner lets
downstream arguments use the additive and scalar laws without rebuilding them locally. -/
@[stacks 00K8 "associated graded semilinear degree map"]
  noncomputable def mapGradeLinear
    (f : R →+* S) (hIJ : I ≤ Ideal.comap f J) (n : ℕ) :
    grade I n →ₛₗ[f] grade J n where
  toFun := mapGrade I J f hIJ n
  map_add' := mapGradeLinear_map_add f hIJ n
  map_smul' := mapGradeLinear_map_smul f hIJ n

/-- Evaluation of the bundled degreewise map agrees with the canonical graded-map view. -/
@[simp, stacks 00K8 "associated graded semilinear degree map evaluation"]
theorem mapGradeLinear_apply
    (f : R →+* S) (hIJ : I ≤ Ideal.comap f J) (n : ℕ) (x : grade I n) :
    mapGradeLinear f hIJ n x = mapGrade I J f hIJ n x := sorry

/-- The quotient-Rees associated graded map is functorial under composition. -/
@[stacks 00K8 "associated graded ring-map composition"]
theorem map_comp
    (f : R →+* S) (g : S →+* T)
    (hIJ : I ≤ Ideal.comap f J)
    (hJK : J ≤ Ideal.comap g K) :
    (map g hJK).comp (map f hIJ) =
      map (g.comp f) (hIJ.trans (Ideal.comap_mono hJK)) := sorry

/-- The degreewise maps are functorial under composition. -/
@[stacks 00K8 "associated graded degree-map composition"]
theorem mapGrade_comp
    (f : R →+* S) (g : S →+* T)
    (hIJ : I ≤ Ideal.comap f J)
    (hJK : J ≤ Ideal.comap g K) (n : ℕ) :
    (mapGrade J K g hJK n) ∘ (mapGrade I J f hIJ n) =
      mapGrade I K (g.comp f) (hIJ.trans (Ideal.comap_mono hJK)) n := sorry

/-- The bundled semilinear degree maps compose to the degree map induced by the composite ring
homomorphism. -/
@[stacks 00K8 "associated graded semilinear degree-map composition"]
theorem mapGradeLinear_comp
    (f : R →+* S) (g : S →+* T)
    (hIJ : I ≤ Ideal.comap f J)
    (hJK : J ≤ Ideal.comap g K) (n : ℕ) :
    -- Local instance justification (defeq pin): the semilinear composition requires the definitional identification of g.comp f.
    letI : RingHomCompTriple f g (g.comp f) := ⟨rfl⟩
    (mapGradeLinear g hJK n).comp (mapGradeLinear f hIJ n) =
      mapGradeLinear (g.comp f) (hIJ.trans (Ideal.comap_mono hJK)) n := sorry

end Ideal.AssociatedGraded

end
