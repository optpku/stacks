module

public import Mathlib.CategoryTheory.NatIso
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import ReasLib.RingTheory.Ideal.Quotient.AlgebraMap
public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType.BaseChange
public import ReasLib.RingTheory.AdicCompletion.ClosedImmersion

/-!
# Closed-immersion base change of topologically finite type algebras

Completed tensor base change to a quotient of a Noetherian ring agrees naturally
with quotienting the algebra by the extended kernel ideal.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open Algebra.TopologicallyFiniteType

universe u

variable {A : Type u} [CommRing A]

namespace CommAlgCat.TopologicallyFiniteType

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
  map f := ObjectProperty.homMk (CommAlgCat.ofHom (Ideal.Quotient.mapAlgHom a f.hom.hom))
  map_id B := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    exact Ideal.Quotient.mapAlgHom_id a
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    exact Ideal.Quotient.mapAlgHom_comp a f.hom.hom g.hom.hom

/-- On objects, `quotIdeal` is the quotient algebra `B ⧸ aB`. -/
theorem quotIdeal_obj [IsNoetherianRing A] (I a : Ideal A) (Ibar : Ideal (A ⧸ a))
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hI : I.map (algebraMap A (A ⧸ a)) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (algebraMap A (A ⧸ a)))
    (B : TopologicallyFiniteType.{u} A I) :
    ((quotIdeal I a Ibar hc hd hI hIbar).obj B).obj =
      CommAlgCat.of (A ⧸ a) (B.obj ⧸ a.map (algebraMap A B.obj)) := sorry

/-- On morphisms, `quotIdeal` is `Ideal.Quotient.mapAlgHom`. -/
theorem quotIdeal_map [IsNoetherianRing A] (I a : Ideal A) (Ibar : Ideal (A ⧸ a))
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hI : I.map (algebraMap A (A ⧸ a)) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (algebraMap A (A ⧸ a)))
    {B B' : TopologicallyFiniteType.{u} A I} (f : B ⟶ B') :
    ((quotIdeal I a Ibar hc hd hI hIbar).map f).hom.hom = Ideal.Quotient.mapAlgHom a f.hom.hom := sorry

/-- Objectwise isomorphism in `C'(A ⧸ a, Ibar)` between completed tensor base
change and the quotient functor `B ↦ B ⧸ aB`. -/
def isoComponent [IsNoetherianRing A] (I a : Ideal A) (Ibar : Ideal (A ⧸ a))
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hI : I.map (algebraMap A (A ⧸ a)) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (algebraMap A (A ⧸ a)))
    (B : TopologicallyFiniteType.{u} A I) :
    (baseChange I Ibar hc hI (IsNoetherian.noetherian Ibar)).obj B ≅
      (quotIdeal I a Ibar hc hd hI hIbar).obj B :=
  isoMk (AdicCompletion.closedImmersionBaseChangeOfCofinal I a Ibar
      (Nat.succ_le_iff.mp hc) (Nat.succ_le_iff.mp hd) hI hIbar)

/-- The underlying algebra map of the component is the canonical completed
tensor-to-quotient equivalence. -/
theorem isoComponent_hom [IsNoetherianRing A] (I a : Ideal A) (Ibar : Ideal (A ⧸ a))
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hI : I.map (algebraMap A (A ⧸ a)) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (algebraMap A (A ⧸ a)))
    (B : TopologicallyFiniteType.{u} A I) :
    (isoComponent I a Ibar hc hd hI hIbar B).hom.hom.hom =
      (AdicCompletion.closedImmersionBaseChangeOfCofinal (B := B.obj) I a Ibar
      (Nat.succ_le_iff.mp hc) (Nat.succ_le_iff.mp hd) hI hIbar).toAlgHom := sorry

/-- The canonical completed tensor-to-quotient components commute with algebra maps. -/
theorem closedImmersionBaseChangeIso_naturality [IsNoetherianRing A]
    (I a : Ideal A) (Ibar : Ideal (A ⧸ a))
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hI : I.map (algebraMap A (A ⧸ a)) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (algebraMap A (A ⧸ a)))
    {B B' : TopologicallyFiniteType.{u} A I} (f : B ⟶ B') :
    (baseChange I Ibar hc hI (IsNoetherian.noetherian Ibar)).map f ≫
        (isoComponent I a Ibar hc hd hI hIbar B').hom =
      (isoComponent I a Ibar hc hd hI hIbar B).hom ≫
        (quotIdeal I a Ibar hc hd hI hIbar).map f := sorry

/-- Over a Noetherian ring, completed tensor base change to a quotient ring with
an ideal cofinal with the extended source ideal is naturally isomorphic to
quotienting each algebra by the extended kernel ideal. -/
def closedImmersionBaseChangeIso [IsNoetherianRing A] (I a : Ideal A) (Ibar : Ideal (A ⧸ a))
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hI : I.map (algebraMap A (A ⧸ a)) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (algebraMap A (A ⧸ a))) :
    baseChange I Ibar hc hI (IsNoetherian.noetherian Ibar) ≅
      quotIdeal I a Ibar hc hd hI hIbar :=
  NatIso.ofComponents (isoComponent I a Ibar hc hd hI hIbar)
    (closedImmersionBaseChangeIso_naturality I a Ibar hc hd hI hIbar)

/-- Components of `closedImmersionBaseChangeIso` are the objectwise identifications
`isoComponent`. -/
theorem closedImmersionBaseChangeIso_app [IsNoetherianRing A] (I a : Ideal A) (Ibar : Ideal (A ⧸ a))
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hI : I.map (algebraMap A (A ⧸ a)) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (algebraMap A (A ⧸ a)))
    (B : TopologicallyFiniteType.{u} A I) :
    (closedImmersionBaseChangeIso I a Ibar hc hd hI hIbar).app B =
      isoComponent I a Ibar hc hd hI hIbar B := sorry

end CommAlgCat.TopologicallyFiniteType
