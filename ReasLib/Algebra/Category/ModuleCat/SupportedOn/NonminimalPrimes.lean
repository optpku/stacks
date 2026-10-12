/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.ClosedSupport
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding

@[expose] public section

open CategoryTheory Set TopologicalSpace

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

variable {A : Type u} [CommRing A]

/-- The nonminimal points of a subset of a prime spectrum, with minimality measured
inside that subset. -/
def nonminimalPrimes (T : Set (PrimeSpectrum A)) : Set (PrimeSpectrum A) :=
  {p | p ∈ T ∧ ∃ q ∈ T, q ≠ p ∧ q ⤳ p}

/-- Membership in `nonminimalPrimes T` is witnessed by a distinct generalization in `T`. -/
theorem mem_nonminimalPrimes_iff {T : Set (PrimeSpectrum A)} {p : PrimeSpectrum A} :
    p ∈ nonminimalPrimes T ↔ p ∈ T ∧ ∃ q ∈ T, q ≠ p ∧ q ⤳ p := sorry

/-- The nonminimal points of `T` form a subset of `T`. -/
theorem nonminimalPrimes_subset (T : Set (PrimeSpectrum A)) : nonminimalPrimes T ⊆ T := sorry

/-- The closed subset `V(f)` of `Spec(A)`, bundled as an object of `Closeds`. -/
def principalClosed (f : A) : Closeds (PrimeSpectrum A) :=
  ⟨PrimeSpectrum.zeroLocus ({f} : Set A), PrimeSpectrum.isClosed_zeroLocus _⟩

/-- The set underlying `principalClosed f` is `V(f)`. -/
theorem coe_principalClosed (f : A) :
    (principalClosed f : Set (PrimeSpectrum A)) =
      PrimeSpectrum.zeroLocus ({f} : Set A) := sorry

/-- A closed subset `Z ⊆ Spec(A)` together with an element `f : A`. -/
def SupportPair (A : Type u) [CommRing A] := Closeds (PrimeSpectrum A) × A

/-- Construct a support pair from a closed subset and an element. -/
def SupportPair.mk (Z : Closeds (PrimeSpectrum A)) (f : A) : SupportPair A := (Z, f)

/-- The closed support `Z` belonging to a support pair `(Z, f)`. -/
def SupportPair.closed (x : SupportPair A) : Closeds (PrimeSpectrum A) := x.1

/-- The element `f` belonging to a support pair `(Z, f)`. -/
def SupportPair.element (x : SupportPair A) : A := x.2

/-- The order key records a pair's closed support and its principal closed subset. -/
def SupportPair.orderKey (x : SupportPair A) :
    Closeds (PrimeSpectrum A) × Closeds (PrimeSpectrum A) :=
  (x.closed, principalClosed x.element)

/-- Support pairs are ordered by simultaneous inclusion of their two closed supports. -/
instance supportPairPreorder : Preorder (SupportPair A) := Preorder.lift SupportPair.orderKey

/-- The full subcategory of pairs `(Z, f)` satisfying `Z ⊆ T` and `Z ∩ V(f) ⊆ T'`. -/
abbrev SupportPairs (T T' : Set (PrimeSpectrum A)) :=
  ObjectProperty.FullSubcategory (fun x : SupportPair A ↦
    (x.closed : Set (PrimeSpectrum A)) ⊆ T ∧
      (x.closed : Set (PrimeSpectrum A)) ∩ (principalClosed x.element : Set _) ⊆ T')

/-- Construct an admissible support pair from a closed subset and an element. -/
def SupportPairs.mk {T T' : Set (PrimeSpectrum A)} (Z : Closeds (PrimeSpectrum A))
    (f : A) (hZ : (Z : Set (PrimeSpectrum A)) ⊆ T)
    (h_inter : (Z : Set (PrimeSpectrum A)) ∩ (principalClosed f : Set _) ⊆ T') :
    SupportPairs T T' :=
  ⟨SupportPair.mk Z f, hZ, h_inter⟩

/-- The closed support belonging to an admissible pair. -/
def SupportPairs.closed {T T' : Set (PrimeSpectrum A)} (x : SupportPairs T T') :
    Closeds (PrimeSpectrum A) :=
  x.obj.closed

/-- The element belonging to an admissible pair. -/
def SupportPairs.element {T T' : Set (PrimeSpectrum A)} (x : SupportPairs T T') : A :=
  x.obj.element

/-- The intersection `Z ∩ V(f)` belonging to an admissible pair `(Z, f)`. -/
def SupportPairs.intersection {T T' : Set (PrimeSpectrum A)} (x : SupportPairs T T') :
    Set (PrimeSpectrum A) :=
  (x.closed : Set (PrimeSpectrum A)) ∩ (principalClosed x.element : Set _)

/-- The defining containment `Z ∩ V(f) ⊆ T'` of an admissible pair. -/
theorem SupportPairs.intersection_subset {T T' : Set (PrimeSpectrum A)}
    (x : SupportPairs T T') : x.intersection ⊆ T' := sorry

/-- Cohomology in fixed support is functorial in the derived coefficient object. -/
noncomputable def cohomologyMap (S : Set (PrimeSpectrum A))
    {K L : DerivedCategory (ModuleCat.{u} A)} (g : K ⟶ L) (i : ℤ) :
    cohomology S K i ⟶ cohomology S L i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
    ((derivedInclusion S).map ((derivedSections S).map g))

/-- The cohomology map induced by enlarging the support. -/
noncomputable def supportCohomologyMap {S S' : Set (PrimeSpectrum A)} (h : S ⊆ S')
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    cohomology S K i ⟶ cohomology S' K i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map (derivedSupportMap h K)

/-- The principal-support object representing `H¹_f(H_Z^(i-1)(M))`. -/
noncomputable def SupportPairs.principalFirstCohomology {T T' : Set (PrimeSpectrum A)}
    (M : ModuleCat.{u} A) (i : ℤ) (x : SupportPairs T T') : ModuleCat.{u} A :=
  cohomology (PrimeSpectrum.zeroLocus ({x.element} : Set A))
    (ModuleCat.single0
      (cohomology (x.closed : Set (PrimeSpectrum A)) (ModuleCat.single0 M) (i - 1))) 1

/-- The map between the closed-support cohomology terms of comparable support pairs. -/
noncomputable def SupportPairs.closedMap {T T' : Set (PrimeSpectrum A)}
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) {x y : SupportPairs T T'}
    (h : x.obj ≤ y.obj) :
    cohomology (x.closed : Set (PrimeSpectrum A)) K i ⟶
      cohomology (y.closed : Set (PrimeSpectrum A)) K i :=
  supportCohomologyMap h.1 K i

/-- The transition map on `H¹_f(H_Z^(i-1)(M))` when both `Z` and `V(f)` increase. -/
noncomputable def SupportPairs.principalFirstMap {T T' : Set (PrimeSpectrum A)}
    (M : ModuleCat.{u} A) (i : ℤ) {x y : SupportPairs T T'} (h : x.obj ≤ y.obj) :
    x.principalFirstCohomology M i ⟶ y.principalFirstCohomology M i :=
  supportCohomologyMap h.2
      (ModuleCat.single0
        (cohomology (x.closed : Set (PrimeSpectrum A)) (ModuleCat.single0 M) (i - 1))) 1 ≫
    cohomologyMap (PrimeSpectrum.zeroLocus ({y.element} : Set A))
      (ModuleCat.single0Functor.map (x.closedMap (ModuleCat.single0 M) (i - 1) h)) 1

/-- The source diagram `(Z, f) ↦ H¹_f(H_Z^(i-1)(M))` over admissible support pairs. -/
noncomputable def principalFirstCohomologyDiagram (T T' : Set (PrimeSpectrum A))
    (M : ModuleCat.{u} A) (i : ℤ) : SupportPairs T T' ⥤ ModuleCat.{u} A where
  obj x := x.principalFirstCohomology M i
  map f := SupportPairs.principalFirstMap M i (leOfHom f.hom)
  map_id := sorry
  map_comp := sorry

/-- Evaluation of the principal-support diagram at an admissible pair. -/
theorem principalFirstCohomologyDiagram_obj (T T' : Set (PrimeSpectrum A))
    (M : ModuleCat.{u} A) (i : ℤ) (x : SupportPairs T T') :
    (principalFirstCohomologyDiagram T T' M i).obj x =
      x.principalFirstCohomology M i := sorry

/-- The map of the principal-support diagram along an inclusion of support pairs. -/
theorem principalFirstCohomologyDiagram_map (T T' : Set (PrimeSpectrum A))
    (M : ModuleCat.{u} A) (i : ℤ) {x y : SupportPairs T T'} (f : x ⟶ y) :
    (principalFirstCohomologyDiagram T T' M i).map f =
      SupportPairs.principalFirstMap M i (leOfHom f.hom) := sorry

/-- The nonminimal points of a specialization-stable subset remain stable under specialization. -/
theorem nonminimalPrimes_stable [IsNoetherianRing A] (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) :
    StableUnderSpecialization (nonminimalPrimes T) := sorry

end CategoryTheory.ModuleCat.SupportedOn
