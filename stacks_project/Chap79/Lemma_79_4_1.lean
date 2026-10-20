module

public import ReasLib.RingTheory.Ideal.Cotangent.Groupoid
import StacksCheckRecall

universe u v w

/- Lemma 79.4.1 (1): The map on cotangent modules induced by composition is the diagonal
followed by the copair induced by the two factor maps. -/
@[stacks 0CKA] #check (Ideal.Cotangent.Groupoid.compositionMap_eq_diagonal :
  ∀ {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C],
    (I : Ideal B) → (J : Ideal C) → (s t : A →+* B) → (e : B →+* A) →
    (l r c : B →+* C) → (e₁ e₂ : C →+* B) →
    I = RingHom.ker e → J = I.map l ⊔ I.map r →
    (h_l : I ≤ J.comap l) → (h_r : I ≤ J.comap r) → (h_c : I ≤ J.comap c) →
    J = I.comap e₁ → J = I.comap e₂ →
    e₁.comp l = t.comp e → e₁.comp r = RingHom.id B →
    e₂.comp l = RingHom.id B → e₂.comp r = s.comp e →
    e₁.comp c = RingHom.id B → e₂.comp c = RingHom.id B →
    Ideal.mapCotangent I J c.toIntAlgHom h_c =
      ((Ideal.mapCotangent I J l.toIntAlgHom h_l).coprod
        (Ideal.mapCotangent I J r.toIntAlgHom h_r)).comp
          ((LinearMap.id : I.Cotangent →ₗ[ℤ] I.Cotangent).prod LinearMap.id))

/- Lemma 79.4.1 (2): The map on the identity cotangent module induced by inversion is
negation. -/
@[stacks 0CKA] #check (Ideal.Cotangent.Groupoid.inverseMap_eq_neg :
  ∀ {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C],
    (I : Ideal B) → (J : Ideal C) → (s t : A →+* B) → (e : B →+* A) →
    (l r c : B →+* C) → (e₁ e₂ : C →+* B) → (i : B →+* B) → (a : C →+* B) →
    I = RingHom.ker e → J = I.map l ⊔ I.map r →
    (h_l : I ≤ J.comap l) → (h_r : I ≤ J.comap r) → (h_c : I ≤ J.comap c) →
    J = I.comap e₁ → J = I.comap e₂ →
    e₁.comp l = t.comp e → e₁.comp r = RingHom.id B →
    e₂.comp l = RingHom.id B → e₂.comp r = s.comp e →
    e₁.comp c = RingHom.id B → e₂.comp c = RingHom.id B →
    (h_i : I ≤ I.comap i) → (h_a : J ≤ I.comap a) →
    a.comp l = RingHom.id B → a.comp r = i → a.comp c = t.comp e →
    Ideal.mapCotangent I I i.toIntAlgHom h_i =
      -(LinearMap.id : I.Cotangent →ₗ[ℤ] I.Cotangent))
