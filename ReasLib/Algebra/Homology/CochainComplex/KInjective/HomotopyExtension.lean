module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-! # Extending nullhomotopies across a short exact sequence into termwise injectives

This is the successor step in the proof of Stacks 079L. Let `0 → K → L → N → 0` be a short
exact sequence of cochain complexes and let `I` be termwise injective. For `f : L ⟶ I` and a
specified nullhomotopy of its restriction to `K`, the homotopy components extend across the
termwise monomorphism `K ⟶ L` by the native injective extension `Injective.factorThru`.
Subtracting the induced null-homotopic map gives a map vanishing on `K`; it descends to the
specified cokernel `N`. A supplied nullhomotopy of that quotient map then yields an actual
nullhomotopy of `f` whose components restrict to the given ones on `K`.

All homotopy components are explicit: no `Nonempty (Homotopy _ _)` or `IsKInjective`
certificate is consumed, and every statement here is proved.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CochainComplex.HomotopyExtension

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
variable {I : CochainComplex C ℤ} [∀ n : ℤ, Injective (I.X n)]
variable (f : S.X₂ ⟶ I) (hK : Homotopy (S.f ≫ f) 0)

include hS

omit [∀ n : ℤ, Injective (I.X n)] in
/-- The degreewise inclusion `K^p ⟶ L^p` of the short exact sequence is monomorphic. -/
lemma mono_f (p : ℤ) : Mono (S.f.f p) := by
  have := hS.mono_f
  infer_instance

/-- The given homotopy components on `K`, extended along `K^p ⟶ L^p` into the injective
`I^q` by the native injective extension. -/
def extendedHom (p q : ℤ) : S.X₂.X p ⟶ I.X q :=
  haveI := mono_f hS p
  Injective.factorThru (hK.hom p q) (S.f.f p)

@[reassoc (attr := simp)]
lemma f_extendedHom (p q : ℤ) : S.f.f p ≫ extendedHom hS f hK p q = hK.hom p q := by
  haveI := mono_f hS p
  exact Injective.comp_factorThru _ _

/-- The null-homotopic map determined by the extended components. -/
def extendedNullHomotopicMap : S.X₂ ⟶ I :=
  Homotopy.nullHomotopicMap' fun p q _ ↦ extendedHom hS f hK p q

/-- The correction of `f` by the extended null-homotopic map. -/
def correction : S.X₂ ⟶ I := f - extendedNullHomotopicMap hS f hK

/-- The corrected map vanishes on the subcomplex `K`. -/
lemma f_correction : S.f ≫ correction hS f hK = 0 := by
  have hnull : S.f ≫ extendedNullHomotopicMap hS f hK = S.f ≫ f := by
    rw [extendedNullHomotopicMap, Homotopy.comp_nullHomotopicMap']
    ext i
    rw [hK.comm i, HomologicalComplex.zero_f_apply, add_zero]
    simp only [Homotopy.nullHomotopicMap', Homotopy.nullHomotopicMap, f_extendedHom]
    congr 2 <;> ext p q <;> split_ifs with h
    all_goals first | rfl | exact (hK.zero p q h).symm
  rw [correction, Preadditive.comp_sub, hnull, sub_self]

/-- The corrected map descends along the specified cokernel `L ⟶ N`. -/
def quotientMap : S.X₃ ⟶ I :=
  hS.gIsCokernel.desc (CokernelCofork.ofπ (correction hS f hK) (f_correction hS f hK))

@[reassoc (attr := simp)]
lemma g_quotientMap : S.g ≫ quotientMap hS f hK = correction hS f hK :=
  Cofork.IsColimit.π_desc hS.gIsCokernel

/-- The explicit homotopy from `f` to its corrected map, with the extended components. -/
def homotopyCorrection : Homotopy f (correction hS f hK) :=
  (Homotopy.ofEq (add_sub_cancel (extendedNullHomotopicMap hS f hK) f).symm).trans
    (((Homotopy.nullHomotopy' fun p q _ ↦ extendedHom hS f hK p q).add
      (Homotopy.refl (correction hS f hK))).trans (Homotopy.ofEq (zero_add _)))

/-- The explicit homotopy from `f` to the pullback of its quotient map. -/
def homotopyQuotient : Homotopy f (S.g ≫ quotientMap hS f hK) :=
  (homotopyCorrection hS f hK).trans (Homotopy.ofEq (g_quotientMap hS f hK).symm)

/-- Stacks 079L, successor step: a nullhomotopy of the quotient map gives an actual
nullhomotopy of `f`, built from the extended components and the quotient components. -/
@[stacks 079L "successor step: extension of a nullhomotopy across a short exact sequence"]
def extend (hN : Homotopy (quotientMap hS f hK) 0) : Homotopy f 0 :=
  (homotopyQuotient hS f hK).trans
    ((hN.compLeft S.g).trans (Homotopy.ofEq (Limits.comp_zero)))

/-- The extended nullhomotopy restricts to the given nullhomotopy on `K`; this is the
compatibility needed to glue stagewise nullhomotopies along a filtration. -/
lemma f_extend_hom (hN : Homotopy (quotientMap hS f hK) 0) (p q : ℤ) :
    S.f.f p ≫ (extend hS f hK hN).hom p q = hK.hom p q := by
  have hfg : S.f.f p ≫ S.g.f p = 0 := by
    rw [← HomologicalComplex.comp_f, S.zero, HomologicalComplex.zero_f_apply]
  simp only [extend, homotopyQuotient, homotopyCorrection, Homotopy.trans_hom,
    Homotopy.add_hom, Homotopy.ofEq_hom, Homotopy.refl_hom, Homotopy.compLeft_hom,
    Homotopy.nullHomotopy'_hom, Pi.zero_apply, zero_add, add_zero,
    Preadditive.comp_add, reassoc_of% hfg, Limits.zero_comp]
  split_ifs with h
  · exact f_extendedHom hS f hK p q
  · rw [Limits.comp_zero, hK.zero p q h]

end CochainComplex.HomotopyExtension
