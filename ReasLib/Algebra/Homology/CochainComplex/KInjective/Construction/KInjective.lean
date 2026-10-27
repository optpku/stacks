/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Construction.Tests
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.HomotopyRecursion

/-! # Encoding bounded tests and assembling replacement nullhomotopies

A small object is presented by the fixed generator coproduct, using one generator map
detecting each proper subobject. Its kernel codes a quotient, whose forward and inverse maps
are cokernel descents. Transporting differentials along these actual quotient isomorphisms
encodes each bounded acyclic complex. The coded cone attachments then give its nullhomotopies.

For a specified small-acyclic subcomplex supply at the same bound, the reduction tower and
native well-order recursion extend these to arbitrary acyclic sources.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe w v u

namespace CochainComplex.KInjectiveResolution.Construction

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- A specified separator witness for a proper subobject, and zero for the top subobject.
The witness existence is proved from the supplied native separator. -/
def detectingMap (X : C) (S : Subobject X) : generator C ⟶ X :=
  open Classical in
  if hS : S = ⊤ then 0 else
    let existsMap : ∃ f : generator C ⟶ X, f ≫ cokernel.π S.arrow ≠ 0 := by
      by_contra! h
      have hz : cokernel.π S.arrow = 0 :=
        (show IsSeparator (generator C) from isSeparator_separator C).def _ _
          (fun f ↦ by simpa only [Limits.comp_zero] using h f)
      -- Local instance justification (proof-local temporary data): Cancellation for this subobject uses the epimorphism just proved from its zero cokernel.
      haveI : Epi S.arrow := Abelian.epi_of_cokernel_π_eq_zero _ hz
      have hi : IsIso S.arrow := isIso_of_mono_of_epi S.arrow
      exact hS ((Subobject.isIso_arrow_iff_eq_top S).mp hi)
    existsMap.choose

/-- The chosen map of a proper subobject is detected by its actual cokernel. -/
lemma detectingMap_cokernel_ne_zero (X : C) (S : Subobject X) (hS : S ≠ ⊤) :
    detectingMap C X S ≫ cokernel.π S.arrow ≠ 0 := by
  classical
  simp only [detectingMap, dif_neg hS]
  exact Classical.choose_spec (p := fun f : generator C ⟶ X ↦ f ≫ cokernel.π S.arrow ≠ 0) _

/-- The cardinal inequality specifies an actual embedding of subobject indices in the fixed
coproduct index. Only the native cardinal-to-embedding correspondence is used. -/
def subobjectIndex (X : C) (hX : Subobject.smallCardinal.{w} X ≤ bound C) :
    Shrink.{w} (Subobject X) ↪ (bound C).out :=
  ((Cardinal.le_def _ _).mp (by simpa using hX)).some

/-- Pad the detecting generator maps by zero to the fixed coproduct index. -/
def presentationComponent (X : C) (hX : Subobject.smallCardinal.{w} X ≤ bound C) :
    (bound C).out → (generator C ⟶ X) :=
  Function.extend (subobjectIndex C X hX)
    (fun s ↦ detectingMap C X ((equivShrink (Subobject X)).symm s)) (fun _ ↦ 0)

/-- The actual coproduct map presenting the specified small object. -/
def presentation (X : C) (hX : Subobject.smallCardinal.{w} X ≤ bound C) :
    generatorCopies C (bound C) ⟶ X :=
  Sigma.desc (presentationComponent C X hX)

/-- Every proper subobject is detected by a summand, so the specified presentation is epi. -/
instance presentation_epi (X : C) (hX : Subobject.smallCardinal.{w} X ≤ bound C) :
    Epi (presentation C X hX) := by
  classical
  let S := imageSubobject (presentation C X hX)
  have htop : S = ⊤ := by
    by_contra hS
    have hcomponent :
        Sigma.ι (fun _ : (bound C).out ↦ generator C)
            (subobjectIndex C X hX (equivShrink (Subobject X) S)) ≫ presentation C X hX =
          detectingMap C X S := by
      simp only [presentation, Sigma.ι_desc, presentationComponent,
        (subobjectIndex C X hX).injective.extend_apply, Equiv.symm_apply_apply]
    have hz : presentation C X hX ≫ cokernel.π S.arrow = 0 := by
      rw [← imageSubobject_arrow_comp (presentation C X hX), Category.assoc]
      exact (congrArg (fun a ↦ factorThruImageSubobject (presentation C X hX) ≫ a)
        (cokernel.condition S.arrow)).trans Limits.comp_zero
    exact detectingMap_cokernel_ne_zero C X S hS (by
      rw [← hcomponent, Category.assoc]
      exact (congrArg (fun a ↦ Sigma.ι (fun _ : (bound C).out ↦ generator C)
        (subobjectIndex C X hX (equivShrink (Subobject X) S)) ≫ a) hz).trans Limits.comp_zero)
  -- Local instance justification (proof-local temporary data): The image inclusion of this presentation is invertible because its image was proved to be the top subobject.
  haveI : IsIso S.arrow := (Subobject.isIso_arrow_iff_eq_top S).mpr htop
  rw [← imageSubobject_arrow_comp (presentation C X hX)]
  exact epi_comp _ _

/-- The code of the actual kernel of the specified presentation. -/
def encodeTerm (X : C) (hX : Subobject.smallCardinal.{w} X ≤ bound C) : TermCode C :=
  equivShrink (Subobject (generatorCopies C (bound C)))
    (kernelSubobject (presentation C X hX))

/-- Decoding the term code recovers precisely the specified kernel subobject. -/
@[simp]
lemma termSubobject_encodeTerm (X : C) (hX : Subobject.smallCardinal.{w} X ≤ bound C) :
    termSubobject C (encodeTerm C X hX) = kernelSubobject (presentation C X hX) := by
  simp [encodeTerm, termSubobject]

/-- The forward quotient map is the cokernel descent of the specified presentation. -/
def encodedTermHom (X : C) (hX : Subobject.smallCardinal.{w} X ≤ bound C) :
    term C (encodeTerm C X hX) ⟶ X :=
  cokernel.desc _ (presentation C X hX) (by
    rw [termSubobject_encodeTerm]
    exact kernelSubobject_arrow_comp _)

/-- The inverse is descent of the actual quotient projection along the specified epi.
It is constructed by the native abelian cokernel universal property. -/
def encodedTermInv (X : C) (hX : Subobject.smallCardinal.{w} X ≤ bound C) :
    X ⟶ term C (encodeTerm C X hX) :=
  Abelian.epiDesc (presentation C X hX)
    (cokernel.π (termSubobject C (encodeTerm C X hX)).arrow) (by
      have hk : kernel.ι (presentation C X hX) =
          (kernelSubobjectIso (presentation C X hX)).inv ≫
            (Subobject.isoOfEq _ _ (termSubobject_encodeTerm C X hX)).inv ≫
            (termSubobject C (encodeTerm C X hX)).arrow := by
        simp only [Subobject.isoOfEq_inv, Subobject.ofLE_arrow,
          kernelSubobject_arrow']
      rw [hk, Category.assoc, Category.assoc, cokernel.condition, comp_zero, comp_zero])

/-- Both directions of the presentation quotient isomorphism are the specified descents. -/
def encodedTermIso (X : C) (hX : Subobject.smallCardinal.{w} X ≤ bound C) :
    term C (encodeTerm C X hX) ≅ X where
  hom := encodedTermHom C X hX
  inv := encodedTermInv C X hX
  hom_inv_id := by
    apply (cancel_epi (cokernel.π (termSubobject C (encodeTerm C X hX)).arrow)).mp
    simp [encodedTermHom, encodedTermInv, Category.assoc, Abelian.comp_epiDesc]
    exact (Category.comp_id _).symm
  inv_hom_id := by
    apply (cancel_epi (presentation C X hX)).mp
    simp [encodedTermHom, encodedTermInv, ← Category.assoc, Abelian.comp_epiDesc]

/-- The lifted termwise cardinal bound is the native small-universe inequality. -/
lemma smallCardinal_le_of_boundedBy (N : CochainComplex C ℤ)
    (hN : SmallAcyclic.BoundedBy (bound C) N) (n : ℤ) :
    Subobject.smallCardinal.{w} (N.X n) ≤ bound C := by
  apply Cardinal.lift_le.{max u v}.mp
  simpa only [Subobject.smallCardinal, Cardinal.lift_mk_shrink'] using hN.2.2 n

/-- Encode the actual terms and differentials using their quotient isomorphisms. -/
def encodeComplex (N : CochainComplex C ℤ) (hN : SmallAcyclic.BoundedBy (bound C) N) :
    ComplexCode C where
  terms n := encodeTerm C (N.X n) (smallCardinal_le_of_boundedBy C N hN n)
  differential n := equivShrink _
    ((encodedTermIso C (N.X n) (smallCardinal_le_of_boundedBy C N hN n)).hom ≫
      N.d n (n + 1) ≫
      (encodedTermIso C (N.X (n + 1)) (smallCardinal_le_of_boundedBy C N hN (n + 1))).inv)
  squareZero n := by
    simp only [decodeHom, Equiv.symm_apply_apply, Category.assoc,
      Iso.inv_hom_id_assoc, HomologicalComplex.d_comp_d_assoc, zero_comp, comp_zero]

/-- The degreewise quotient isomorphisms identify the encoded complex with the given one. -/
def encodedComplexIso (N : CochainComplex C ℤ)
    (hN : SmallAcyclic.BoundedBy (bound C) N) : (encodeComplex C N hN).complex ≅ N :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ encodedTermIso C (N.X n) (smallCardinal_le_of_boundedBy C N hN n))
    (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      simp [encodeComplex, ComplexCode.complex, decodeHom])

/-- The encoded complex is a member of the explicit small acyclic test family. -/
def encodeTest (N : CochainComplex C ℤ)
    (hN : SmallAcyclic.BoundedBy (bound C) N) : TestCode C :=
  ⟨encodeComplex C N hN, by
    constructor
    · exact fun i ↦ (hN.2.1 i).of_iso (encodedComplexIso C N hN).symm
    · obtain ⟨n, hn⟩ := hN.1
      exact ⟨n, isStrictlyLE_of_iso (encodedComplexIso C N hN).symm n⟩⟩

/-- The specified test complex is isomorphic to the actual bounded acyclic complex. -/
def encodedTestIso (N : CochainComplex C ℤ)
    (hN : SmallAcyclic.BoundedBy (bound C) N) : testComplex C (encodeTest C N hN) ≅ N :=
  encodedComplexIso C N hN

/-- Transport the explicit coded cone contraction to a specified small acyclic source. -/
def boundedNullHomotopy (K N : CochainComplex C ℤ)
    (hN : SmallAcyclic.BoundedBy (bound C) N) (f : N ⟶ (replacement C).obj K) :
    Homotopy f 0 :=
  (Homotopy.ofEq (by simp)).trans
    (((testNullHomotopy C K (encodeTest C N hN)
      ((encodedTestIso C N hN).hom ≫ f)).compLeft
      (encodedTestIso C N hN).inv).trans (Homotopy.ofEq Limits.comp_zero))

/-- The transported nullhomotopy precomposes the coded components with the explicit inverse. -/
@[simp]
lemma boundedNullHomotopy_hom (K N : CochainComplex C ℤ)
    (hN : SmallAcyclic.BoundedBy (bound C) N) (f : N ⟶ (replacement C).obj K) (p q : ℤ) :
    (boundedNullHomotopy C K N hN f).hom p q =
      (encodedTestIso C N hN).inv.f p ≫
        (testNullHomotopy C K (encodeTest C N hN) ((encodedTestIso C N hN).hom ≫ f)).hom p q := by
  simp [boundedNullHomotopy]

/-- The actual replacement has injective terms, as proved by its generator lifting property. -/
instance replacement_injective (K : CochainComplex C ℤ) (n : ℤ) :
    Injective (((replacement C).obj K).X n) := replacement_term_injective C K n

/-- A supplied reduction tower gives the actual nullhomotopy of every map to the replacement. -/
def nullHomotopyOfReduction (K M : CochainComplex C ℤ)
    (R : AcyclicReduction M (bound C)) (f : M ⟶ (replacement C).obj K) : Homotopy f 0 :=
  R.nullHomotopy (boundedNullHomotopy C K) f

/-- Construct a nullhomotopy from an actual small-subcomplex supply, for an arbitrary
unbounded acyclic source. -/
def nullHomotopyOfSupply (S : SmallAcyclic.SubcomplexSupply C (bound C))
    (K M : CochainComplex C ℤ) (hM : M.Acyclic) (f : M ⟶ (replacement C).obj K) :
    Homotopy f 0 :=
  nullHomotopyOfReduction C K M (AcyclicReduction.ofSupply S hM) f

/-- The concrete supply-based nullhomotopies prove K-injectivity of the replacement. -/
theorem isKInjectiveOfSupply (S : SmallAcyclic.SubcomplexSupply C (bound C))
    (K : CochainComplex C ℤ) : ((replacement C).obj K).IsKInjective where
  nonempty_homotopy_zero f hM := ⟨nullHomotopyOfSupply C S K _ hM f⟩

end CochainComplex.KInjectiveResolution.Construction
