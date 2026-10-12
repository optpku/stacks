/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cotangent modules under algebra equivalences

The two `Ideal.mapCotangent` maps induced by an algebra equivalence combine
into a canonical linear equivalence of cotangent modules.

@stack 00TS
-/

universe u v w

namespace Ideal.Cotangent

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

namespace MapAlgEquiv

/-- The forward cotangent map induced by an `R`-algebra equivalence. -/
noncomputable def forward (I : Ideal A) (e : A ≃ₐ[R] B) :
    I.Cotangent →ₗ[R] (I.map e.toRingHom).Cotangent :=
  I.mapCotangent (I.map e.toRingHom) e.toAlgHom Ideal.le_comap_map

/-- The inverse-direction cotangent map induced by an `R`-algebra equivalence. -/
noncomputable def backward (I : Ideal A) (e : A ≃ₐ[R] B) :
    (I.map e.toRingHom).Cotangent →ₗ[R] I.Cotangent :=
  (I.map e.toRingHom).mapCotangent I e.symm.toAlgHom
    (Ideal.map_comap_of_equiv e.toRingEquiv).le

/-- The forward and backward cotangent maps induced by an algebra equivalence compose to the
identity on the image cotangent module. -/
theorem forward_comp_backward (I : Ideal A) (e : A ≃ₐ[R] B) :
    forward I e ∘ₗ backward I e = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
  simp only [LinearMap.comp_apply, backward, forward,
    Ideal.mapCotangent_toCotangent, LinearMap.id_apply]
  congr 1
  ext
  exact e.apply_symm_apply x

/-- The backward and forward cotangent maps induced by an algebra equivalence compose to the
identity on the original cotangent module. -/
theorem backward_comp_forward (I : Ideal A) (e : A ≃ₐ[R] B) :
    backward I e ∘ₗ forward I e = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
  simp only [LinearMap.comp_apply, backward, forward,
    Ideal.mapCotangent_toCotangent, LinearMap.id_apply]
  congr 1
  ext
  exact e.symm_apply_apply x

end MapAlgEquiv

/-- An `R`-algebra equivalence transports the cotangent module of an ideal to that of its image.

This is the reusable algebra-equivalence naturality form of `Ideal.mapCotangent`. -/
@[stacks 00TS "cotangent transport under algebra equivalence"]
noncomputable def mapAlgEquiv (I : Ideal A) (e : A ≃ₐ[R] B) :
    I.Cotangent ≃ₗ[R] (I.map e.toRingHom).Cotangent :=
  LinearEquiv.ofLinear (MapAlgEquiv.forward I e) (MapAlgEquiv.backward I e)
    (MapAlgEquiv.forward_comp_backward I e)
    (MapAlgEquiv.backward_comp_forward I e)

/-- `mapAlgEquiv` sends a cotangent generator to the generator represented by its image. -/
@[simp]
theorem mapAlgEquiv_toCotangent (I : Ideal A) (e : A ≃ₐ[R] B) (x : I) :
    mapAlgEquiv I e (Ideal.toCotangent I x) =
      Ideal.toCotangent (I.map e.toRingHom) ⟨e x, Ideal.mem_map_of_mem e.toRingHom x.2⟩ := by
  rfl

end Ideal.Cotangent
