module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Algebra maps between quotients by extended ideals

An algebra homomorphism induces a homomorphism over the quotient of the base
ring between the quotients by an extended ideal.
-/

@[expose] public section

universe u v w x

namespace Ideal.Quotient

variable {A : Type u} [CommRing A]

/-- An `A`-algebra homomorphism induces an `A ⧸ a`-algebra homomorphism between
quotients by the extension of `a`. -/
def mapAlgHom (a : Ideal A) {B : Type v} {B' : Type w}
    [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B'] (f : B →ₐ[A] B') :
    B ⧸ a.map (algebraMap A B) →ₐ[A ⧸ a] B' ⧸ a.map (algebraMap A B') where
  toRingHom :=
    Ideal.quotientMap (a.map (algebraMap A B')) f.toRingHom
      (Ideal.map_le_iff_le_comap.mp (le_of_eq
        ((Ideal.map_map (algebraMap A B) f.toRingHom).trans
          (congrArg (fun hom ↦ a.map hom) f.comp_algebraMap))))
  commutes' := by
    intro r
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact congrArg (Ideal.Quotient.mk (a.map (algebraMap A B'))) (f.commutes r)

/-- The induced quotient algebra map sends the class of `b` to the class of `f b`. -/
theorem mapAlgHom_mk (a : Ideal A) {B : Type v} {B' : Type w}
    [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B'] (f : B →ₐ[A] B') (b : B) :
    mapAlgHom a f (Ideal.Quotient.mk (a.map (algebraMap A B)) b) =
      Ideal.Quotient.mk (a.map (algebraMap A B')) (f b) := sorry

/-- The algebra map induced on quotients by the identity is the identity. -/
theorem mapAlgHom_id (a : Ideal A) {B : Type v} [CommRing B] [Algebra A B] :
    mapAlgHom a (AlgHom.id A B) = AlgHom.id (A ⧸ a) (B ⧸ a.map (algebraMap A B)) :=
  sorry

/-- Induced quotient algebra maps preserve composition. -/
theorem mapAlgHom_comp (a : Ideal A) {B : Type v} {B' : Type w} {B'' : Type x}
    [CommRing B] [CommRing B'] [CommRing B'']
    [Algebra A B] [Algebra A B'] [Algebra A B'']
    (f : B →ₐ[A] B') (g : B' →ₐ[A] B'') :
    mapAlgHom a (g.comp f) = (mapAlgHom a g).comp (mapAlgHom a f) := sorry

end Ideal.Quotient
