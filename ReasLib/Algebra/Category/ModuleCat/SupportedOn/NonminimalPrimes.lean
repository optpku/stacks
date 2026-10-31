/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
    p ∈ nonminimalPrimes T ↔ p ∈ T ∧ ∃ q ∈ T, q ≠ p ∧ q ⤳ p := Iff.rfl

/-- The nonminimal points of `T` form a subset of `T`. -/
theorem nonminimalPrimes_subset (T : Set (PrimeSpectrum A)) : nonminimalPrimes T ⊆ T :=
  fun _ hp ↦ hp.1

/-- The closed subset `V(f)` of `Spec(A)`, bundled as an object of `Closeds`. -/
def principalClosed (f : A) : Closeds (PrimeSpectrum A) :=
  ⟨PrimeSpectrum.zeroLocus ({f} : Set A), PrimeSpectrum.isClosed_zeroLocus _⟩

/-- The set underlying `principalClosed f` is `V(f)`. -/
theorem coe_principalClosed (f : A) :
    (principalClosed f : Set (PrimeSpectrum A)) =
      PrimeSpectrum.zeroLocus ({f} : Set A) := rfl

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
    (x : SupportPairs T T') : x.intersection ⊆ T' := x.property.2

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

set_option backward.isDefEq.respectTransparency false in
private theorem derivedSupportMap_naturality {S S' : Set (PrimeSpectrum A)} (h : S ⊆ S')
    {K L : DerivedCategory (ModuleCat.{u} A)} (g : K ⟶ L) :
    (derivedInclusion S).map ((derivedSections S).map g) ≫ derivedSupportMap h L =
      derivedSupportMap h K ≫ (derivedInclusion S').map ((derivedSections S').map g) := by
  let e : (changeSupport h).mapDerivedCategory ⋙ derivedInclusion S' ≅ derivedInclusion S :=
    (ExactFunctor.MapDerivedCategory.compFunctorIso (changeSupport h) (exactInclusion S')).symm ≪≫
      ExactFunctor.MapDerivedCategory.mapIso (changeSupportCompInclusionIso h)
  have hn := e.hom.naturality ((derivedSections S).map g)
  have hi := e.inv.naturality ((derivedSections S).map g)
  have hc := (derivedAdjunction S).counit.naturality g
  dsimp only [Functor.comp_map, Functor.id_map] at hn hi hc
  have hsq :
      (derivedInclusion S').map
          ((changeSupport h).mapDerivedCategory.map ((derivedSections S).map g)) ≫
        (e.hom.app ((derivedSections S).obj L) ≫ (derivedAdjunction S).counit.app L) =
      (e.hom.app ((derivedSections S).obj K) ≫ (derivedAdjunction S).counit.app K) ≫ g := by
    rw [← Category.assoc, hn, Category.assoc, hc, Category.assoc]
  have hm := (derivedAdjunction S').homEquiv_naturality_left_square
    ((changeSupport h).mapDerivedCategory.map ((derivedSections S).map g))
    (e.hom.app ((derivedSections S).obj L) ≫ (derivedAdjunction S).counit.app L)
    (e.hom.app ((derivedSections S).obj K) ≫ (derivedAdjunction S).counit.app K) g hsq
  change (derivedInclusion S).map ((derivedSections S).map g) ≫
      (e.inv.app ((derivedSections S).obj L) ≫ (derivedInclusion S').map
        ((derivedAdjunction S').homEquiv _ _
          (e.hom.app ((derivedSections S).obj L) ≫ (derivedAdjunction S).counit.app L))) =
    (e.inv.app ((derivedSections S).obj K) ≫ (derivedInclusion S').map
      ((derivedAdjunction S').homEquiv _ _
        (e.hom.app ((derivedSections S).obj K) ≫ (derivedAdjunction S).counit.app K))) ≫
      (derivedInclusion S').map ((derivedSections S').map g)
  rw [← Category.assoc, hi, Category.assoc, ← Functor.map_comp, hm,
    Functor.map_comp, Category.assoc]


set_option backward.isDefEq.respectTransparency false in
private theorem supportCohomologyMap_comp {S S' S'' : Set (PrimeSpectrum A)}
    (h : S ⊆ S') (h' : S' ⊆ S'') (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    supportCohomologyMap (h.trans h') K i =
      supportCohomologyMap h K i ≫ supportCohomologyMap h' K i := by
  dsimp only [supportCohomologyMap]
  rw [derivedSupportMap_comp, Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem cohomologyMap_comp (S : Set (PrimeSpectrum A))
    {K L N : DerivedCategory (ModuleCat.{u} A)} (g : K ⟶ L) (g' : L ⟶ N) (i : ℤ) :
    cohomologyMap S (g ≫ g') i = cohomologyMap S g i ≫ cohomologyMap S g' i := by
  simp only [cohomologyMap, Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem supportCohomologyMap_naturality {S S' : Set (PrimeSpectrum A)}
    (h : S ⊆ S') {K L : DerivedCategory (ModuleCat.{u} A)} (g : K ⟶ L) (i : ℤ) :
    cohomologyMap S g i ≫ supportCohomologyMap h L i =
      supportCohomologyMap h K i ≫ cohomologyMap S' g i := by
  dsimp only [cohomologyMap, supportCohomologyMap]
  simpa only [Functor.map_comp] using
    congrArg ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map)
      (derivedSupportMap_naturality h g)

set_option backward.isDefEq.respectTransparency false in
private theorem SupportPairs.principalFirstMap_comp {T T' : Set (PrimeSpectrum A)}
    (M : ModuleCat.{u} A) (i : ℤ) {x y z : SupportPairs T T'}
    (hxy : x.obj ≤ y.obj) (hyz : y.obj ≤ z.obj) :
    SupportPairs.principalFirstMap M i (hxy.trans hyz) =
      SupportPairs.principalFirstMap M i hxy ≫ SupportPairs.principalFirstMap M i hyz := by
  have hc : x.closedMap (ModuleCat.single0 M) (i - 1) (hxy.trans hyz) =
      x.closedMap (ModuleCat.single0 M) (i - 1) hxy ≫
        y.closedMap (ModuleCat.single0 M) (i - 1) hyz :=
    supportCohomologyMap_comp hxy.1 hyz.1 _ _
  have hp : supportCohomologyMap (hxy.trans hyz).2
        (ModuleCat.single0 (cohomology (x.closed : Set _) (ModuleCat.single0 M) (i - 1))) 1 =
      supportCohomologyMap hxy.2
        (ModuleCat.single0 (cohomology (x.closed : Set _) (ModuleCat.single0 M) (i - 1))) 1 ≫
      supportCohomologyMap hyz.2
        (ModuleCat.single0 (cohomology (x.closed : Set _) (ModuleCat.single0 M) (i - 1))) 1 :=
    supportCohomologyMap_comp hxy.2 hyz.2 _ _
  have hn := supportCohomologyMap_naturality hyz.2
    (ModuleCat.single0Functor.map (x.closedMap (ModuleCat.single0 M) (i - 1) hxy)) 1
  dsimp only [SupportPairs.principalFirstMap]
  rw [hp, hc, Functor.map_comp, cohomologyMap_comp]
  simpa only [Category.assoc, SupportPair.orderKey, SupportPair.element,
    SupportPairs.element, principalClosed, Closeds.coe_mk] using congrArg
    (fun k ↦ supportCohomologyMap hxy.2
      (ModuleCat.single0 (cohomology (x.closed : Set _) (ModuleCat.single0 M) (i - 1))) 1 ≫
      k ≫ cohomologyMap (PrimeSpectrum.zeroLocus ({z.element} : Set A))
        (ModuleCat.single0Functor.map (y.closedMap (ModuleCat.single0 M) (i - 1) hyz)) 1) hn.symm

/-- The source diagram `(Z, f) ↦ H¹_f(H_Z^(i-1)(M))` over admissible support pairs. -/
noncomputable def principalFirstCohomologyDiagram (T T' : Set (PrimeSpectrum A))
    (M : ModuleCat.{u} A) (i : ℤ) : SupportPairs T T' ⥤ ModuleCat.{u} A where
  obj x := x.principalFirstCohomology M i
  map f := SupportPairs.principalFirstMap M i (leOfHom f.hom)
  map_id x := by
    dsimp only [SupportPairs.principalFirstMap, SupportPairs.closedMap,
      supportCohomologyMap, cohomologyMap, SupportPair.orderKey,
      SupportPairs.closed, SupportPairs.element, SupportPair.closed, SupportPair.element,
      principalClosed]
    simp only [derivedSupportMap_id, Functor.map_id]
    change (𝟙 (x.principalFirstCohomology M i)) ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  map_comp f g := by
    change SupportPairs.principalFirstMap M i
      ((leOfHom f.hom).trans (leOfHom g.hom)) = _
    exact SupportPairs.principalFirstMap_comp M i (leOfHom f.hom) (leOfHom g.hom)

/-- Evaluation of the principal-support diagram at an admissible pair. -/
theorem principalFirstCohomologyDiagram_obj (T T' : Set (PrimeSpectrum A))
    (M : ModuleCat.{u} A) (i : ℤ) (x : SupportPairs T T') :
    (principalFirstCohomologyDiagram T T' M i).obj x =
      x.principalFirstCohomology M i := rfl

/-- The map of the principal-support diagram along an inclusion of support pairs. -/
theorem principalFirstCohomologyDiagram_map (T T' : Set (PrimeSpectrum A))
    (M : ModuleCat.{u} A) (i : ℤ) {x y : SupportPairs T T'} (f : x ⟶ y) :
    (principalFirstCohomologyDiagram T T' M i).map f =
      SupportPairs.principalFirstMap M i (leOfHom f.hom) := rfl

/-- The nonminimal points of a specialization-stable subset remain stable under specialization. -/
theorem nonminimalPrimes_stable [IsNoetherianRing A] (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) :
    StableUnderSpecialization (nonminimalPrimes T) := by
  intro p r hpr hp
  obtain ⟨hpT, q, hqT, hqp, hqp_spec⟩ := hp
  refine ⟨hT hpr hpT, q, hqT, ?_, hqp_spec.trans hpr⟩
  intro hqr
  apply hqp
  apply le_antisymm
  · exact (PrimeSpectrum.le_iff_specializes q p).mpr hqp_spec
  · exact (PrimeSpectrum.le_iff_specializes p q).mpr (by simpa only [hqr] using hpr)

end CategoryTheory.ModuleCat.SupportedOn
