module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Ideal.Cotangent

@[expose] public section

/-!
# Cotangent maps for groupoid rings

The groupoid composition and inversion laws induce the diagonal and negation maps on the
cotangent modules of the identity ideals.
-/

universe u v w

namespace Ideal.Cotangent.Groupoid

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]

/-- If two unit-section maps identify `J` with the pullback of `I`, then the cotangent map
induced by composition is the copair of the two factor maps after the diagonal. -/
theorem compositionMap_eq_diagonal
    (I : Ideal B) (J : Ideal C) (s t : A →+* B) (e : B →+* A)
    (l r c : B →+* C) (e₁ e₂ : C →+* B)
    (h_kernel : I = RingHom.ker e) (h_generated : J = I.map l ⊔ I.map r)
    (h_l : I ≤ J.comap l) (h_r : I ≤ J.comap r) (h_c : I ≤ J.comap c)
    (h_e₁ : J = I.comap e₁) (h_e₂ : J = I.comap e₂)
    (h_e₁_l : e₁.comp l = t.comp e) (h_e₁_r : e₁.comp r = RingHom.id B)
    (h_e₂_l : e₂.comp l = RingHom.id B) (h_e₂_r : e₂.comp r = s.comp e)
    (h_e₁_c : e₁.comp c = RingHom.id B) (h_e₂_c : e₂.comp c = RingHom.id B) :
    Ideal.mapCotangent I J c.toIntAlgHom h_c =
      ((Ideal.mapCotangent I J l.toIntAlgHom h_l).coprod
        (Ideal.mapCotangent I J r.toIntAlgHom h_r)).comp
          ((LinearMap.id : I.Cotangent →ₗ[ℤ] I.Cotangent).prod LinearMap.id) := sorry

/-- Under the groupoid composition and inverse laws, inversion acts by negation on the
cotangent module of the identity ideal. -/
theorem inverseMap_eq_neg
    (I : Ideal B) (J : Ideal C) (s t : A →+* B) (e : B →+* A)
    (l r c : B →+* C) (e₁ e₂ : C →+* B) (i : B →+* B) (a : C →+* B)
    (h_kernel : I = RingHom.ker e) (h_generated : J = I.map l ⊔ I.map r)
    (h_l : I ≤ J.comap l) (h_r : I ≤ J.comap r) (h_c : I ≤ J.comap c)
    (h_e₁ : J = I.comap e₁) (h_e₂ : J = I.comap e₂)
    (h_e₁_l : e₁.comp l = t.comp e) (h_e₁_r : e₁.comp r = RingHom.id B)
    (h_e₂_l : e₂.comp l = RingHom.id B) (h_e₂_r : e₂.comp r = s.comp e)
    (h_e₁_c : e₁.comp c = RingHom.id B) (h_e₂_c : e₂.comp c = RingHom.id B)
    (h_i : I ≤ I.comap i) (h_a : J ≤ I.comap a)
    (h_a_l : a.comp l = RingHom.id B) (h_a_r : a.comp r = i)
    (h_a_c : a.comp c = t.comp e) :
    Ideal.mapCotangent I I i.toIntAlgHom h_i =
      -(LinearMap.id : I.Cotangent →ₗ[ℤ] I.Cotangent) := sorry

end Ideal.Cotangent.Groupoid
