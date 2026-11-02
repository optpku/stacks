/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.IdealPower.Torsion
public import ReasLib.Algebra.Module.IdealPower.Quotient
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Module
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
Canonical-source candidate DATA leaf for the strict-complex part of Stacks 0954.
This candidate is uncompiled in this review; the owner-controlled Longmen gate remains pending.

All modules use the entry's actual `ModuleCat.{u} A`, with `A : Type u`.
`J` is an arbitrary, unbounded, integer-indexed cochain complex. No injectivity,
finite generation, Noetherianity, or weak proregularity is needed for these maps.
The original derived statements retain their `I.FG` hypothesis.

The source in each Hom complex is concentrated in degree zero. Consequently
the usual differential `d_J f - (-1)^q f d_source` reduces to `d_J f` in
every integer degree, including negative degrees; `singleRead_d` records this.

No desired existence proposition is used to choose any of the new DATA.
The imported generic APIs have existing Prop proof debt, detailed in REPORT.md.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex

namespace CochainComplex.IdealPowerTorsion

variable {A : Type u} [CommRing A]

/-- Use the exact quotient carrier already used by the 0954 entry. -/
abbrev quotientStage (I : Ideal A) (n : ℕ) : ModuleCat.{u} A :=
  Ideal.PowerQuotient.positiveStage I (ModuleCat.of A A) n

def quotientClass (I : Ideal A) (n : ℕ) (a : A) : quotientStage I n :=
  Submodule.Quotient.mk a

def quotientOne (I : Ideal A) (n : ℕ) : quotientStage I n :=
  quotientClass I n 1

/-- Reduction from exponent `n + 2` to exponent `n + 1`, not the reverse. -/
abbrev quotientStep (I : Ideal A) (n : ℕ) :
    quotientStage I (n + 1) ⟶ quotientStage I n :=
  Ideal.PowerQuotient.positiveStep I (ModuleCat.of A A) n

@[simp]
theorem quotientStep_class (I : Ideal A) (n : ℕ) (a : A) :
    (quotientStep I n).hom (quotientClass I (n + 1) a) = quotientClass I n a := rfl

@[simp]
theorem quotientStep_one (I : Ideal A) (n : ℕ) :
    (quotientStep I n).hom (quotientOne I (n + 1)) = quotientOne I n := rfl

/-- The class of one is killed by the *specified* denominator ideal. -/
theorem smul_quotientOne_zero (I : Ideal A) (n : ℕ) (a : A)
    (ha : a ∈ I ^ (n + 1)) : a • quotientOne I n = 0 := by
  change (Submodule.Quotient.mk (a • (1 : A)) :
    A ⧸ (I ^ (n + 1) • (⊤ : Submodule A A))) = 0
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact Submodule.smul_mem_smul ha (Submodule.mem_top : (1 : A) ∈ (⊤ : Submodule A A))

/-- Ordinary evaluation at the class of one, with no selected witness. -/
def evalOneLinear (I : Ideal A) (n : ℕ) (M : ModuleCat.{u} A) :
    (quotientStage I n →ₗ[A] M) →ₗ[A] M where
  toFun f := f (quotientOne I n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evalOne_annihilated (I : Ideal A) (n : ℕ) (M : ModuleCat.{u} A)
    (f : quotientStage I n →ₗ[A] M) (a : A) (ha : a ∈ I ^ (n + 1)) :
    a • evalOneLinear I n M f = 0 := by
  change a • f (quotientOne I n) = 0
  rw [← f.map_smul, smul_quotientOne_zero I n a ha, f.map_zero]

theorem evalOne_mem (I : Ideal A) (n : ℕ) (M : ModuleCat.{u} A)
    (f : quotientStage I n →ₗ[A] M) :
    evalOneLinear I n M f ∈ I.primaryComponent M := by
  rw [Ideal.primaryComponent_mem]
  refine ⟨n + 1, ?_⟩
  rw [Submodule.mem_torsionBySet_iff]
  intro a
  exact evalOne_annihilated I n M f a.val a.property

/-- Evaluation with codomain restricted by the preceding annihilator proof. -/
def evalOneTorsion (I : Ideal A) (n : ℕ) (M : ModuleCat.{u} A) :
    (quotientStage I n →ₗ[A] M) →ₗ[A] I.primaryComponent M :=
  (evalOneLinear I n M).codRestrict (I.primaryComponent M) (evalOne_mem I n M)

@[simp]
theorem evalOneTorsion_coe (I : Ideal A) (n : ℕ) (M : ModuleCat.{u} A)
    (f : quotientStage I n →ₗ[A] M) :
    (evalOneTorsion I n M f : M) = f (quotientOne I n) := rfl

/-- Explicit quotient descent of `a ↦ a • x` for a supplied annihilation proof.
This is useful for the later termwise colimit proof; no exponent is chosen here. -/
def fromAnnihilated (I : Ideal A) (n : ℕ) (M : ModuleCat.{u} A) (x : M)
    (hx : ∀ a ∈ I ^ (n + 1), a • x = 0) : quotientStage I n →ₗ[A] M :=
  (I ^ (n + 1) • (⊤ : Submodule A A)).liftQ
    (LinearMap.toSpanSingleton A M x) (by
      apply Submodule.smul_le.mpr
      intro a ha b _hb
      change (a * b) • x = 0
      rw [mul_smul, smul_comm a b x, hx a ha, smul_zero])

@[simp]
theorem fromAnnihilated_class (I : Ideal A) (n : ℕ) (M : ModuleCat.{u} A)
    (x : M) (hx : ∀ a ∈ I ^ (n + 1), a • x = 0) (a : A) :
    fromAnnihilated I n M x hx (quotientClass I n a) = a • x := rfl

@[simp]
theorem evalOne_fromAnnihilated (I : Ideal A) (n : ℕ) (M : ModuleCat.{u} A)
    (x : M) (hx : ∀ a ∈ I ^ (n + 1), a • x = 0) :
    evalOneLinear I n M (fromAnnihilated I n M x hx) = x := by
  change fromAnnihilated I n M x hx (quotientClass I n 1) = x
  rw [fromAnnihilated_class, one_smul]

abbrev singleSource (I : Ideal A) (n : ℕ) : CochainComplex (ModuleCat.{u} A) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).obj (quotientStage I n)

abbrev singleStep (I : Ideal A) (n : ℕ) : singleSource I (n + 1) ⟶ singleSource I n :=
  (CochainComplex.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).map (quotientStep I n)

/-- The existing module-valued Hom complex, rather than a new surrogate carrier. -/
abbrev strictStage (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℕ) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  CochainComplex.HomComplex.moduleComplex A (singleSource I n) J

/-- Quotient precomposition is the successor arrow in the direct diagram. -/
def strictStep (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℕ) :
    strictStage I J n ⟶ strictStage I J (n + 1) :=
  CochainComplex.HomComplex.map A (singleStep I n) (𝟙 J)

/-- An actual strict diagram: all other arrows are specified finite composites. -/
def strictDiagram (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) :
    ℕ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  Functor.ofSequence (strictStep I J)

@[simp]
theorem strictDiagram_step (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (n : ℕ) :
    (strictDiagram I J).map (homOfLE (Nat.le_add_right n 1)) = strictStep I J n :=
  Functor.ofSequence_map_homOfLE_succ (strictStep I J) n

/-- The sequence constructor has this actual stage; retain its identity-on-stage transport. -/
def strictDiagramObjIso (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℕ) :
    (strictDiagram I J).obj n ≅ strictStage I J n :=
  eqToIso (by rfl)

/-- Read the source-degree-zero component using Mathlib's single-complex equivalence. -/
def singleRead (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℕ) (q : ℤ) :
    (strictStage I J n).X q →ₗ[A] (quotientStage I n →ₗ[A] J.X q) where
  toFun z := ((Cochain.fromSingleEquiv
    (X := quotientStage I n) (K := J) (zero_add q)) z).hom
  map_add' z w := by
    rfl
  map_smul' a z := by
    rfl

@[simp]
theorem singleRead_fromSingleMk (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (n : ℕ) (q : ℤ) (f : quotientStage I n ⟶ J.X q) :
    singleRead I J n q (Cochain.fromSingleMk f (zero_add q)) = f.hom := by
  change ((Cochain.fromSingleEquiv (zero_add q))
    (Cochain.fromSingleMk f (zero_add q))).hom = f.hom
  rw [Cochain.fromSingleEquiv_fromSingleMk]

theorem strict_d_apply (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (n : ℕ) (q : ℤ) (z : (strictStage I J n).X q) :
    ((strictStage I J n).d q (q + 1)).hom z = δ q (q + 1) z := by
  change ((CochainComplex.HomComplex.moduleComplex A (singleSource I n) J).d
    q (q + 1)).hom z = δ q (q + 1) z
  rewrite [CochainComplex.HomComplex.moduleComplex_d]
  change CochainComplex.HomComplex.moduleDifferential A (singleSource I n) J q z =
    δ q (q + 1) z
  exact CochainComplex.HomComplex.moduleDifferential_apply A (singleSource I n) J q z

/-- There is no lost negative-degree sign: the source differential is zero. -/
theorem singleRead_d (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (n : ℕ) (q : ℤ) (z : (strictStage I J n).X q) :
    singleRead I J n (q + 1) (((strictStage I J n).d q (q + 1)).hom z) =
      (J.d q (q + 1)).hom.comp (singleRead I J n q z) := by
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z q (zero_add q)
  rewrite [strict_d_apply,
    Cochain.δ_fromSingleMk f (zero_add q) (q + 1) (q + 1) (zero_add (q + 1)),
    singleRead_fromSingleMk, singleRead_fromSingleMk]
  rfl

/-- The two-variable map formula specialized to the actual single source. -/
theorem singleRead_map (I : Ideal A)
    {J L : CochainComplex (ModuleCat.{u} A) ℤ} {n m : ℕ}
    (a : quotientStage I m ⟶ quotientStage I n) (g : J ⟶ L) (q : ℤ)
    (z : (strictStage I J n).X q) :
    singleRead I L m q
        (((CochainComplex.HomComplex.map A
          ((CochainComplex.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).map a) g).f q).hom z) =
      (g.f q).hom.comp ((singleRead I J n q z).comp a.hom) := by
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z q (zero_add q)
  rewrite [CochainComplex.HomComplex.map_f_apply,
    ← Cochain.fromSingleMk_precomp, ← Cochain.fromSingleMk_postcomp,
    singleRead_fromSingleMk, singleRead_fromSingleMk]
  rfl

@[simp]
theorem singleRead_step (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (n : ℕ) (q : ℤ) (z : (strictStage I J n).X q) :
    singleRead I J (n + 1) q (((strictStep I J n).f q).hom z) =
      (singleRead I J n q z).comp (quotientStep I n).hom := by
  simpa [strictStep, singleStep] using singleRead_map I (quotientStep I n) (𝟙 J) q z

/-- The existing primary-component coreflector followed by its existing inclusion. -/
abbrev gammaFunctor (I : Ideal A) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  ((CategoryTheory.ModuleCat.IdealPowerTorsion.coreflector I) ⋙
    CategoryTheory.ModuleCat.IdealPowerTorsion.inclusion I).mapHomologicalComplex
      (ComplexShape.up ℤ)

abbrev gamma (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  (gammaFunctor I).obj J

/-- Identify the degreewise coreflector-inclusion object with its actual primary component. -/
def gammaTermIso (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (q : ℤ) :
    (gamma I J).X q ≅ ModuleCat.of A (I.primaryComponent (J.X q)) :=
  eqToIso (by rfl)

/-- The specified primary-component inclusion, with its actual component transport. -/
def gammaTermInclusion (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (q : ℤ) :
    (gamma I J).X q ⟶ J.X q :=
  (gammaTermIso I J q).hom ≫
    CategoryTheory.ModuleCat.IdealPowerTorsion.subtypeHom I (J.X q)

theorem gammaTermInclusion_injective
    (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (q : ℤ) :
    Function.Injective (gammaTermInclusion I J q).hom := by
  intro x y h
  apply (gammaTermIso I J q).toLinearEquiv.injective
  apply Subtype.ext
  exact h

/-- At degree `q`, evaluate the read linear map at `[1]` and restrict its codomain. -/
def evalTerm (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℕ) (q : ℤ) :
    (strictStage I J n).X q →ₗ[A] (gamma I J).X q :=
  (evalOneTorsion I n (J.X q)).comp (singleRead I J n q)

@[simp]
theorem evalTerm_coe (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (n : ℕ) (q : ℤ) (z : (strictStage I J n).X q) :
    (gammaTermInclusion I J q).hom (evalTerm I J n q z) =
      singleRead I J n q z (quotientOne I n) := rfl

/-- Actual chain map to the termwise primary-component complex. -/
def evaluation (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℕ) :
    strictStage I J n ⟶ gamma I J where
  f q := ModuleCat.ofHom (evalTerm I J n q)
  comm' := by
    intro p q hpq
    obtain rfl : p + 1 = q := hpq
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply gammaTermInclusion_injective I J (p + 1)
    change (J.d p (p + 1)).hom
        (evalOneLinear I n (J.X p) (singleRead I J n p z)) =
      evalOneLinear I n (J.X (p + 1))
        (singleRead I J n (p + 1) (((strictStage I J n).d p (p + 1)).hom z))
    rw [singleRead_d]
    rfl

theorem evaluation_annihilated (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (n : ℕ) (q : ℤ) (z : (strictStage I J n).X q)
    (a : A) (ha : a ∈ I ^ (n + 1)) :
    a • (gammaTermInclusion I J q).hom (((evaluation I J n).f q).hom z) = 0 := by
  change a • evalOneLinear I n (J.X q) (singleRead I J n q z) = 0
  exact evalOne_annihilated I n (J.X q) (singleRead I J n q z) a ha

/-- Successor compatibility is exactly reduction taking `[1]` to `[1]`. -/
theorem evaluation_step (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℕ) :
    strictStep I J n ≫ evaluation I J (n + 1) = evaluation I J n := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply gammaTermInclusion_injective I J q
  change evalOneLinear I (n + 1) (J.X q)
      (singleRead I J (n + 1) q (((strictStep I J n).f q).hom z)) =
    evalOneLinear I n (J.X q) (singleRead I J n q z)
  rw [singleRead_step]
  change singleRead I J n q z ((quotientStep I n).hom (quotientOne I (n + 1))) =
    singleRead I J n q z (quotientOne I n)
  rw [quotientStep_one]

/-- Explicit postcomposition in a supplied cochain map `g : J ⟶ L`. -/
def stagePost (I : Ideal A) (n : ℕ)
    {J L : CochainComplex (ModuleCat.{u} A) ℤ} (g : J ⟶ L) :
    strictStage I J n ⟶ strictStage I L n :=
  CochainComplex.HomComplex.map A (𝟙 (singleSource I n)) g

@[simp]
theorem singleRead_post (I : Ideal A) (n : ℕ)
    {J L : CochainComplex (ModuleCat.{u} A) ℤ} (g : J ⟶ L) (q : ℤ)
    (z : (strictStage I J n).X q) :
    singleRead I L n q (((stagePost I n g).f q).hom z) =
      (g.f q).hom.comp (singleRead I J n q z) := by
  simpa [stagePost] using singleRead_map I (𝟙 (quotientStage I n)) g q z

theorem stagePost_step (I : Ideal A) (n : ℕ)
    {J L : CochainComplex (ModuleCat.{u} A) ℤ} (g : J ⟶ L) :
    strictStep I J n ≫ stagePost I (n + 1) g =
      stagePost I n g ≫ strictStep I L n := by
  simp only [strictStep, stagePost, ← CochainComplex.HomComplex.map_comp,
    Category.id_comp, Category.comp_id]

/-- Naturality as an actual transformation of the specified direct diagrams. -/
def diagramMap (I : Ideal A)
    {J L : CochainComplex (ModuleCat.{u} A) ℤ} (g : J ⟶ L) :
    strictDiagram I J ⟶ strictDiagram I L :=
  NatTrans.ofSequence
    (F := strictDiagram I J) (G := strictDiagram I L)
    (fun n ↦ (strictDiagramObjIso I J n).hom ≫ stagePost I n g ≫
      (strictDiagramObjIso I L n).inv) (by
      intro n
      rewrite [strictDiagram_step I J n, strictDiagram_step I L n]
      change
        strictStep I J n ≫
            (𝟙 (strictStage I J (n + 1)) ≫ stagePost I (n + 1) g ≫
              𝟙 (strictStage I L (n + 1))) =
          (𝟙 (strictStage I J n) ≫ stagePost I n g ≫ 𝟙 (strictStage I L n)) ≫
            strictStep I L n
      simpa only [Category.id_comp, Category.comp_id] using stagePost_step I n g)

theorem evaluation_naturality (I : Ideal A) (n : ℕ)
    {J L : CochainComplex (ModuleCat.{u} A) ℤ} (g : J ⟶ L) :
    stagePost I n g ≫ evaluation I L n =
      evaluation I J n ≫ (gammaFunctor I).map g := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply gammaTermInclusion_injective I L q
  change evalOneLinear I n (L.X q)
      (singleRead I L n q (((stagePost I n g).f q).hom z)) =
    (g.f q).hom (evalOneLinear I n (J.X q) (singleRead I J n q z))
  rw [singleRead_post]
  rfl

/-- Specified cocone DATA only; no `IsColimit` assertion is made here. -/
def torsionCocone (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) :
    Cocone (strictDiagram I J) where
  pt := gamma I J
  ι := NatTrans.ofSequence
    (F := strictDiagram I J) (G := (Functor.const ℕ).obj (gamma I J))
    (fun n ↦ (strictDiagramObjIso I J n).hom ≫ evaluation I J n) (by
      intro n
      rewrite [strictDiagram_step I J n]
      change
        strictStep I J n ≫ (𝟙 (strictStage I J (n + 1)) ≫ evaluation I J (n + 1)) =
          (𝟙 (strictStage I J n) ≫ evaluation I J n) ≫ 𝟙 (gamma I J)
      simpa only [Category.id_comp, Category.comp_id] using evaluation_step I J n)

theorem torsionCocone_naturality (I : Ideal A)
    {J L : CochainComplex (ModuleCat.{u} A) ℤ} (g : J ⟶ L) :
    diagramMap I g ≫ (torsionCocone I L).ι =
      (torsionCocone I J).ι ≫ (Functor.const ℕ).map ((gammaFunctor I).map g) := by
  apply NatTrans.ext
  funext n
  change
    ((strictDiagramObjIso I J n).hom ≫ stagePost I n g ≫
        (strictDiagramObjIso I L n).inv) ≫
        ((strictDiagramObjIso I L n).hom ≫ evaluation I L n) =
      ((strictDiagramObjIso I J n).hom ≫ evaluation I J n) ≫ (gammaFunctor I).map g
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun k : strictStage I J n ⟶ gamma I L ↦ (strictDiagramObjIso I J n).hom ≫ k)
      (evaluation_naturality I n g)

end CochainComplex.IdealPowerTorsion

end
