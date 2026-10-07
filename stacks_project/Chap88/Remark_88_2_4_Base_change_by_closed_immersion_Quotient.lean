module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import stacks_project.Chap88.«88_2_0_2_TopologicallyFiniteType»
public import stacks_project.Chap88.«88_2_3_2_BaseChange»
public import stacks_project.Chap88.«88_2_4_1_ClosedImmersion»

/-!
# Quotient form of closed-immersion base change on C'

For a Noetherian pair `(A, I)` and an ideal `a`, a cofinal ideal `Ibar ⊂ A ⧸ a`
induces the computational functor `B ↦ B ⧸ aB` on topologically finite type
algebras, naturally isomorphic to completed tensor base change.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open Algebra.TopologicallyFiniteType

universe u

variable {A : Type u} [CommRing A]

namespace CommAlgCat.TopologicallyFiniteType

/-- Compatibility of an `A`-algebra map with the extended ideals of `a`. -/
theorem quotMap_le_comap (a : Ideal A) {B B' : Type u}
    [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B'] (f : B →ₐ[A] B') :
    a.map (algebraMap A B) ≤ (a.map (algebraMap A B')).comap f.toRingHom := sorry

/-- The unbundled quotient map `B ⧸ aB →ₐ[A ⧸ a] B' ⧸ aB'` induced by an
`A`-algebra homomorphism. -/
def quotMap (a : Ideal A) {B B' : Type u}
    [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B'] (f : B →ₐ[A] B') :
    B ⧸ a.map (algebraMap A B) →ₐ[A ⧸ a] B' ⧸ a.map (algebraMap A B') where
  toRingHom :=
    Ideal.quotientMap (a.map (algebraMap A B')) f.toRingHom (quotMap_le_comap a f)
  commutes' := sorry

/-- `quotMap` sends the class of `b` to the class of `f b`. -/
theorem quotMap_mk (a : Ideal A) {B B' : Type u}
    [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B'] (f : B →ₐ[A] B') (b : B) :
    quotMap a f (Ideal.Quotient.mk (a.map (algebraMap A B)) b) =
      Ideal.Quotient.mk (a.map (algebraMap A B')) (f b) := sorry

/-- `quotMap` of the identity is the identity. -/
theorem quotMap_id (a : Ideal A) {B : Type u} [CommRing B] [Algebra A B] :
    quotMap a (AlgHom.id A B) = AlgHom.id (A ⧸ a) (B ⧸ a.map (algebraMap A B)) :=
  sorry

/-- `quotMap` preserves composition of `A`-algebra homomorphisms. -/
theorem quotMap_comp (a : Ideal A) {B B' B'' : Type u}
    [CommRing B] [CommRing B'] [CommRing B'']
    [Algebra A B] [Algebra A B'] [Algebra A B'']
    (f : B →ₐ[A] B') (g : B' →ₐ[A] B'') :
    quotMap a (g.comp f) = (quotMap a g).comp (quotMap a f) := sorry

/-- Under two-sided cofinality of `Ibar` with `I (A ⧸ a)`, the quotient `B ⧸ aB`
of an object of `C'(A, I)` lies in `C'(A ⧸ a, Ibar)`. -/
theorem quotIdeal_topologicallyFiniteType [IsNoetherianRing A]
    (I a : Ideal A) (Ibar : Ideal (A ⧸ a)) {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hI : I.map (algebraMap A (A ⧸ a)) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (algebraMap A (A ⧸ a)))
    {B : Type u} [CommRing B] [Algebra A B] [Algebra.TopologicallyFiniteType I B] :
    Algebra.TopologicallyFiniteType Ibar (B ⧸ a.map (algebraMap A B)) := sorry

/-- The computational closed-immersion base-change functor `C'(A, I) ⥤ C'(A ⧸ a, Ibar)`,
sending `B` to `B ⧸ aB`. -/
def quotIdeal [IsNoetherianRing A] (I a : Ideal A) (Ibar : Ideal (A ⧸ a))
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hI : I.map (algebraMap A (A ⧸ a)) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (algebraMap A (A ⧸ a))) :
    TopologicallyFiniteType.{u} A I ⥤ TopologicallyFiniteType.{u} (A ⧸ a) Ibar where
  obj B :=
    { obj := CommAlgCat.of (A ⧸ a) (B.obj ⧸ a.map (algebraMap A B.obj))
      property := quotIdeal_topologicallyFiniteType I a Ibar hc hd hI hIbar }
  map f := ObjectProperty.homMk (CommAlgCat.ofHom (quotMap a f.hom.hom))
  map_id := sorry
  map_comp := sorry

/-- On objects, `quotIdeal` is the quotient algebra `B ⧸ aB`. -/
theorem quotIdeal_obj [IsNoetherianRing A] (I a : Ideal A) (Ibar : Ideal (A ⧸ a))
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hI : I.map (algebraMap A (A ⧸ a)) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (algebraMap A (A ⧸ a)))
    (B : TopologicallyFiniteType.{u} A I) :
    ((quotIdeal I a Ibar hc hd hI hIbar).obj B).obj =
      CommAlgCat.of (A ⧸ a) (B.obj ⧸ a.map (algebraMap A B.obj)) := sorry

/-- On morphisms, `quotIdeal` is `quotMap`. -/
theorem quotIdeal_map [IsNoetherianRing A] (I a : Ideal A) (Ibar : Ideal (A ⧸ a))
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hI : I.map (algebraMap A (A ⧸ a)) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (algebraMap A (A ⧸ a)))
    {B B' : TopologicallyFiniteType.{u} A I} (f : B ⟶ B') :
    ((quotIdeal I a Ibar hc hd hI hIbar).map f).hom.hom = quotMap a f.hom.hom := sorry

/-- Canonical `A ⧸ a`-algebra identification of completed tensor base change
with the quotient `B ⧸ aB`. -/
def isoComponentEquiv [IsNoetherianRing A] (I a : Ideal A) (Ibar : Ideal (A ⧸ a))
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hI : I.map (algebraMap A (A ⧸ a)) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (algebraMap A (A ⧸ a)))
    (B : Type u) [CommRing B] [Algebra A B] [Algebra.TopologicallyFiniteType I B] :
    completedBaseChange A Ibar B ≃ₐ[A ⧸ a] B ⧸ a.map (algebraMap A B) :=
  @AdicCompletion.closedImmersionBaseChange A B _ _ _ a Ibar
    (IsAdicComplete.quotIdealMap I a Ibar (Nat.succ_le_iff.mp hc)
      (Nat.succ_le_iff.mp hd) hI hIbar)

/-- `isoComponentEquiv` is the closed-immersion identification of equation 88.2.4.1. -/
theorem isoComponentEquiv_eq [IsNoetherianRing A] (I a : Ideal A)
    (Ibar : Ideal (A ⧸ a)) {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hI : I.map (algebraMap A (A ⧸ a)) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (algebraMap A (A ⧸ a)))
    (B : Type u) [CommRing B] [Algebra A B] [Algebra.TopologicallyFiniteType I B] :
    isoComponentEquiv I a Ibar hc hd hI hIbar B =
      @AdicCompletion.closedImmersionBaseChange A B _ _ _ a Ibar
        (IsAdicComplete.quotIdealMap I a Ibar (Nat.succ_le_iff.mp hc)
          (Nat.succ_le_iff.mp hd) hI hIbar) := sorry

/-- Objectwise isomorphism in `C'(A ⧸ a, Ibar)` between completed tensor base
change and the quotient functor `B ↦ B ⧸ aB`. -/
def isoComponent [IsNoetherianRing A] (I a : Ideal A) (Ibar : Ideal (A ⧸ a))
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hI : I.map (algebraMap A (A ⧸ a)) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (algebraMap A (A ⧸ a)))
    (B : TopologicallyFiniteType.{u} A I) :
    (baseChange I Ibar hc hI (IsNoetherian.noetherian Ibar)).obj B ≅
      (quotIdeal I a Ibar hc hd hI hIbar).obj B :=
  isoMk (isoComponentEquiv I a Ibar hc hd hI hIbar B.obj)

/-- The underlying `A ⧸ a`-algebra map of `isoComponent` is `isoComponentEquiv`. -/
theorem isoComponent_hom [IsNoetherianRing A] (I a : Ideal A) (Ibar : Ideal (A ⧸ a))
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hI : I.map (algebraMap A (A ⧸ a)) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (algebraMap A (A ⧸ a)))
    (B : TopologicallyFiniteType.{u} A I) :
    (isoComponent I a Ibar hc hd hI hIbar B).hom.hom.hom =
      (isoComponentEquiv I a Ibar hc hd hI hIbar B.obj).toAlgHom := sorry

end CommAlgCat.TopologicallyFiniteType
