/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Extension.FirstOrder
public import ReasLib.RingTheory.Extension.SectionQuotient
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Unramified.Basic
import ReasLib.RingTheory.Extension.Infinitesimal
import ReasLib.RingTheory.Extension.Quotient
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Universal First-Order Thickenings from the Self-Presentation

For a formally unramified algebra `R → S`, the polynomial self-presentation
of `S` admits a canonical quotient construction that is universal among
first-order thickenings.  Only the stable construction data are public; the
correction and uniqueness argument remains private proof infrastructure.

@stack 04EB
-/

@[expose] public section

noncomputable section

open Algebra
open Algebra.Extension
open scoped TensorProduct

universe u v z

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

namespace Algebra.Extension.FirstOrder.SelfPresentation

/-- Helper for Lemma 10.149.1: for the canonical polynomial presentation of `S`, the conormal map
onto the Kähler differentials is surjective when `R → S` is formally unramified. -/
private lemma cotangentComplex_surjective [Algebra.FormallyUnramified R S] :
    Function.Surjective ((Generators.self R S).toExtension.cotangentComplex) := by
  let P : Extension R S := (Generators.self R S).toExtension
  have hExact : LinearMap.ker P.toKaehler = LinearMap.range P.cotangentComplex := by
    exact (LinearMap.exact_iff).mp P.exact_cotangentComplex_toKaehler
  have hKer : LinearMap.ker P.toKaehler = ⊤ := by
    rw [LinearMap.ker_eq_top]
    ext x
    exact Subsingleton.elim _ _
  exact LinearMap.range_eq_top.mp <| hExact.symm.trans hKer

/-- Helper for Lemma 10.149.1: the cotangent complex of the canonical polynomial presentation of
`S` admits an `S`-linear section when `R → S` is formally unramified. -/
private lemma cotangentComplex_has_section [Algebra.FormallyUnramified R S] :
    ∃ l : (Generators.self R S).toExtension.CotangentSpace →ₗ[S]
        (Generators.self R S).toExtension.Cotangent,
      (Generators.self R S).toExtension.cotangentComplex ∘ₗ l = LinearMap.id := by
  let P : Extension R S := (Generators.self R S).toExtension
  obtain ⟨l, hl⟩ :=
    P.cotangentComplex.exists_rightInverse_of_surjective <|
      LinearMap.range_eq_top.mpr (cotangentComplex_surjective (R := R) (S := S))
  exact ⟨l, hl⟩

/-- Helper for Lemma 10.149.1: the canonical self presentation lifts any map `S → A/I` across a
square-zero quotient because its source ring is a polynomial algebra. -/
private lemma exists_polynomial_lift
    {A : Type*} [CommRing A] [Algebra R A]
    (I : Ideal A) (hI : I ^ 2 = ⊥) (f : S →ₐ[R] A ⧸ I) :
    ∃ β : (Generators.self R S).toExtension.Ring →ₐ[R] A,
      (Ideal.Quotient.mkₐ R I).comp β =
        f.comp (IsScalarTower.toAlgHom R (Generators.self R S).toExtension.Ring S) := by
  let P : Extension R S := (Generators.self R S).toExtension
  -- Local instance justification (defeq pin): `P.Ring` is the polynomial
  -- self-presentation, but instance search does not unfold the local abbreviation.
  let _ : Algebra.FormallySmooth R P.Ring := by
    change Algebra.FormallySmooth R (MvPolynomial S R)
    infer_instance
  -- Lift the composite `P.Ring → S → A/I` using formal smoothness of the polynomial ring.
  simpa [P] using
    (Algebra.FormallySmooth.exists_lift
      (R := R)
      (A := P.Ring)
      (B := A)
      I
      ⟨2, hI⟩
      (f.comp (IsScalarTower.toAlgHom R P.Ring S)))

/-- Helper for Lemma 10.149.1: a polynomial lift to `A` packages as a morphism from the canonical
self presentation into the square-zero quotient extension `A → A ⧸ I`. -/
private lemma polynomial_lift_to_extension_hom
    {A : Type*} [CommRing A] [Algebra R A]
    (I : Ideal A) (f : S →ₐ[R] A ⧸ I)
    (β : (Generators.self R S).toExtension.Ring →ₐ[R] A)
    (hβ : (Ideal.Quotient.mkₐ R I).comp β =
      f.comp (IsScalarTower.toAlgHom R (Generators.self R S).toExtension.Ring S)) :
    let P0 : Extension R S := (Generators.self R S).toExtension
    -- Local instance justification (noncanonical choice): the `S`-algebra
    -- structure on `A ⧸ I` is determined by the explicit map `f`.
    let _ : Algebra S (A ⧸ I) := f.toAlgebra
    let Q : Extension R (A ⧸ I) := Ideal.Quotient.extension R I
    ∃ φ : P0.Hom Q, φ.toAlgHom = β := by
  intro P0 _ Q
  -- Repackage the lifted algebra map as a hom between the source and target extensions.
  refine ⟨Extension.Hom.ofAlgHom β ?_, rfl⟩
  have hf : IsScalarTower.toAlgHom R S (A ⧸ I) = f := by
    ext
    rfl
  rw [Ideal.Quotient.extension_toAlgHom, hf]
  exact hβ

/-- Helper for Lemma 10.149.1: over a square-zero target extension, any prescribed cotangent-space
map from the self presentation is realized by correcting a fixed owner lift on the self
generators. -/
private lemma exists_corrected_extension_hom
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    (Q : Extension R S') (hQsq : Q.ker ^ 2 = ⊥)
    (φ : ((Generators.self R S).toExtension).Hom Q)
    (u : ((Generators.self R S).toExtension).CotangentSpace →ₗ[S] Q.Cotangent) :
    ∃ φu : ((Generators.self R S).toExtension).Hom Q, φu.sub φ = u := by
  let G : Generators R S S := Generators.self R S
  let P0 : Extension R S := G.toExtension
  let δ : S → Q.ker := fun s ↦
    (Q.kerCotangentEquiv hQsq).symm (u (G.cotangentSpaceBasis s))
  have hδ : ∀ s, Extension.Cotangent.mk (δ s) = u (G.cotangentSpaceBasis s) := by
    intro s
    -- The chosen kernel correction represents the prescribed cotangent value on each basis vector.
    change
      (Q.kerCotangentEquiv hQsq)
          ((Q.kerCotangentEquiv hQsq).symm (u (G.cotangentSpaceBasis s))) =
        _
    simp
  let ψ : P0.Ring →ₐ[R] Q.Ring :=
    MvPolynomial.aeval fun s ↦ φ.toAlgHom (.X s) + (δ s : Q.Ring)
  have hψX : ∀ s, ψ (MvPolynomial.X s) = φ.toAlgHom (MvPolynomial.X s) + (δ s : Q.Ring) := by
    intro s
    -- On each self generator, the corrected owner map is the old value plus the kernel error.
    change MvPolynomial.aeval (fun t : S ↦ φ.toAlgHom (MvPolynomial.X t) + (δ t : Q.Ring))
        (MvPolynomial.X s) = _
    simp
  have hψcomm :
      (IsScalarTower.toAlgHom R Q.Ring S').comp ψ =
        (IsScalarTower.toAlgHom R S S').comp (IsScalarTower.toAlgHom R P0.Ring S) := by
    apply MvPolynomial.algHom_ext
    intro s
    -- The correction lies in the kernel, so it disappears after passing to the quotient algebra.
    change algebraMap Q.Ring S' (ψ (MvPolynomial.X s)) =
      algebraMap S S' ((algebraMap P0.Ring S) (MvPolynomial.X s))
    rw [hψX]
    rw [map_add,
      show algebraMap Q.Ring S' (δ s : Q.Ring) = 0 by exact (δ s).2,
      add_zero]
    simp [P0, G]
  let φu : P0.Hom Q := Extension.Hom.ofAlgHom ψ hψcomm
  have hsubToKer_X : ∀ s, (φu.subToKer φ) (MvPolynomial.X s) = δ s := by
    intro s
    -- On each generator, the difference between the corrected and original lifts is exactly `δ s`.
    apply Subtype.ext
    change ψ (MvPolynomial.X s) - φ.toAlgHom (MvPolynomial.X s) = (δ s : Q.Ring)
    rw [hψX]
    abel
  refine ⟨φu, ?_⟩
  apply G.cotangentSpaceBasis.ext
  intro s
  -- Compare both cotangent-space maps on the canonical basis of the self presentation.
  calc
    φu.sub φ (G.cotangentSpaceBasis s) =
        Extension.Cotangent.mk ((φu.subToKer φ) (MvPolynomial.X s)) := by
          rw [Generators.cotangentSpaceBasis_apply]
          exact Extension.Hom.sub_one_tmul (f := φu) (g := φ) (x := MvPolynomial.X s)
    _ = Extension.Cotangent.mk (δ s) := by rw [hsubToKer_X s]
    _ = u (G.cotangentSpaceBasis s) := hδ s

/-- Helper for Lemma 10.149.1: correcting a self-presentation lift by the negative cotangent
obstruction forces the corrected cotangent map to vanish on the chosen section. -/
private lemma corrected_extension_hom_cotangent_vanish
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    (Q : Extension R S') (hQsq : Q.ker ^ 2 = ⊥)
    (φ : ((Generators.self R S).toExtension).Hom Q)
    (l : ((Generators.self R S).toExtension).CotangentSpace →ₗ[S]
      ((Generators.self R S).toExtension).Cotangent)
    (hl : ((Generators.self R S).toExtension).cotangentComplex ∘ₗ l = LinearMap.id) :
    ∃ φu : ((Generators.self R S).toExtension).Hom Q,
      (Extension.Cotangent.map φu) ∘ₗ l = 0 := by
  let P0 : Extension R S := (Generators.self R S).toExtension
  let u : P0.CotangentSpace →ₗ[S] Q.Cotangent := -((Extension.Cotangent.map φ) ∘ₗ l)
  obtain ⟨φu, hsub⟩ :=
    exists_corrected_extension_hom (R := R) (S := S) Q hQsq φ u
  refine ⟨φu, ?_⟩
  apply LinearMap.ext
  intro x
  have hmap := LinearMap.congr_fun (Extension.Cotangent.map_sub_map φu φ) (l x)
  have hsplit : P0.cotangentComplex (l x) = x := by
    -- The chosen section splits the cotangent complex on the nose.
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hl x
  have hdiff :
      Extension.Cotangent.map φu (l x) - Extension.Cotangent.map φ (l x) =
        -Extension.Cotangent.map φ (l x) := by
    -- The correction was defined to cancel the original cotangent obstruction.
    calc
      Extension.Cotangent.map φu (l x) - Extension.Cotangent.map φ (l x) =
          φu.sub φ (P0.cotangentComplex (l x)) := by
            simpa [LinearMap.comp_apply] using hmap
      _ = u (P0.cotangentComplex (l x)) := by rw [hsub]
      _ = u x := by rw [hsplit]
      _ = -Extension.Cotangent.map φ (l x) := by rfl
  have hfinal := hdiff
  abel_nf at hfinal
  simpa using hfinal

/-- Helper for Lemma 10.149.1: a map from the canonical self presentation into a square-zero
extension kills the square of the presentation kernel. -/
private lemma extension_hom_zero_of_mem_ker_sq
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    (Q : Extension R S') (hQsq : Q.ker ^ 2 = ⊥)
    (φ : ((Generators.self R S).toExtension).Hom Q)
    {x : ((Generators.self R S).toExtension).Ring}
    (hx : x ∈ ((Generators.self R S).toExtension).ker ^ 2) :
    φ.toAlgHom x = 0 := by
  let P0 : Extension R S := (Generators.self R S).toExtension
  have hker :
      P0.ker ≤ Ideal.comap φ.toAlgHom.toRingHom Q.ker := by
    intro y hy
    -- Elements of the source kernel still map to the target kernel.
    change algebraMap Q.Ring S' (φ.toRingHom y) = 0
    rw [φ.algebraMap_toRingHom]
    have hy0 : algebraMap P0.Ring S y = 0 := by
      simpa [P0, RingHom.mem_ker] using hy
    rw [hy0]
    simp
  have hsq :
      P0.ker ^ 2 ≤ Ideal.comap φ.toAlgHom.toRingHom (Q.ker ^ 2) :=
    (Ideal.pow_right_mono hker 2).trans <|
      Ideal.le_comap_pow (f := φ.toAlgHom.toRingHom) (K := Q.ker) 2
  have hxsq : φ.toAlgHom x ∈ Q.ker ^ 2 := by
    simpa [P0, Ideal.mem_comap] using hsq hx
  -- Square-zero of the target kernel forces the image to vanish.
  simpa [hQsq, Ideal.mem_bot] using hxsq

/-- Helper for Lemma 10.149.1: after correcting the owner map into a square-zero target, the map
descends from the polynomial self presentation to its infinitesimal quotient by `ker²`. -/
private noncomputable def infinitesimal_lift
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    (Q : Extension R S') (hQsq : Q.ker ^ 2 = ⊥)
    (φ : ((Generators.self R S).toExtension).Hom Q) :
    ((Generators.self R S).toExtension.infinitesimal.Ring) →ₐ[R] Q.Ring :=
  let P0 : Extension R S := (Generators.self R S).toExtension
  Ideal.Quotient.liftₐ (P0.ker ^ 2) φ.toAlgHom
    (fun _ hx ↦
      extension_hom_zero_of_mem_ker_sq
        (R := R) (S := S) Q hQsq φ hx)

/-- Helper for Lemma 10.149.1: the descended infinitesimal lift still reduces to the original
target map on `S`. -/
private lemma infinitesimal_lift_comp_eq
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    (Q : Extension R S') (hQsq : Q.ker ^ 2 = ⊥)
    (φ : ((Generators.self R S).toExtension).Hom Q) :
    (IsScalarTower.toAlgHom R Q.Ring S').comp
        (infinitesimal_lift (R := R) (S := S) Q hQsq φ) =
      (IsScalarTower.toAlgHom R S S').comp
        (IsScalarTower.toAlgHom R ((Generators.self R S).toExtension.infinitesimal.Ring) S) := by
  let P0 : Extension R S := (Generators.self R S).toExtension
  -- Compare the two quotient maps after precomposing with `P0.Ring → P0.Ring / P0.ker²`.
  refine Ideal.Quotient.algHom_ext (R₁ := R) <| AlgHom.ext fun x ↦ ?_
  change algebraMap Q.Ring S'
      ((infinitesimal_lift (R := R) (S := S) Q hQsq φ)
        (Ideal.Quotient.mk (P0.ker ^ 2) x)) =
    algebraMap S S' (algebraMap P0.Ring S x)
  rw [infinitesimal_lift]
  change algebraMap Q.Ring S' (φ.toAlgHom x) = algebraMap S S' (algebraMap P0.Ring S x)
  exact φ.algebraMap_toRingHom x

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Lemma 10.149.1: evaluating the descended infinitesimal lift on the explicit
cotangent representative agrees with the square-zero target's conormal representative of the
transported cotangent class. -/
private lemma infinitesimal_lift_apply_cotangent_representative
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    (Q : Extension R S') (hQsq : Q.ker ^ 2 = ⊥)
    (φ : ((Generators.self R S).toExtension).Hom Q)
    (y : ((Generators.self R S).toExtension).Cotangent) :
    infinitesimal_lift (R := R) (S := S) Q hQsq φ
        (Algebra.Extension.Infinitesimal.cotangentIdealSubtype
          ((Generators.self R S).toExtension)
          (Ideal.cotangentEquivIdeal ((Generators.self R S).toExtension.ker)
            (((Generators.self R S).toExtension).cotangentEquivCotangentKer y))) =
      (((Q.kerCotangentEquiv hQsq).symm
        (Extension.Cotangent.map φ y) : Q.ker) : Q.Ring) := by
  let P0 : Extension R S := (Generators.self R S).toExtension
  obtain ⟨x, rfl⟩ := Extension.Cotangent.mk_surjective y
  have hxker :
      φ.toAlgHom x ∈ Q.ker := by
    -- The image of a source-kernel element is again in the target kernel.
    change algebraMap Q.Ring S' (φ.toAlgHom x) = 0
    rw [show φ.toAlgHom x = φ.toRingHom x by rfl, φ.algebraMap_toRingHom]
    simpa using congrArg (algebraMap S S') x.2
  -- Rewrite the source representative to the quotient class of `x`, then evaluate the quotient lift.
  change
    infinitesimal_lift (R := R) (S := S) Q hQsq φ
        (Ideal.Quotient.mk (P0.ker ^ 2) x) =
      (((Q.kerCotangentEquiv hQsq).symm
        (Extension.Cotangent.mk ⟨φ.toAlgHom x, hxker⟩) : Q.ker) : Q.Ring)
  rw [infinitesimal_lift]
  change φ.toAlgHom x =
    (((Q.kerCotangentEquiv hQsq).symm
      (Extension.Cotangent.mk ⟨φ.toAlgHom x, hxker⟩) : Q.ker) : Q.Ring)
  exact congrArg Subtype.val
    (Q.kerCotangentEquiv_symm_mk hQsq ⟨φ.toAlgHom x, hxker⟩).symm

/-- Helper for Lemma 10.149.1: if the corrected cotangent obstruction vanishes on the chosen
section, then each explicit section generator maps to zero under the descended infinitesimal lift. -/
private lemma section_generator_image_eq_zero_of_cotangent_vanish
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    (Q : Extension R S') (hQsq : Q.ker ^ 2 = ⊥)
    (φ : ((Generators.self R S).toExtension).Hom Q)
    (l : ((Generators.self R S).toExtension).CotangentSpace →ₗ[S]
      ((Generators.self R S).toExtension).Cotangent)
    (hφ : (Extension.Cotangent.map φ) ∘ₗ l = 0)
    (x : ((Generators.self R S).toExtension).CotangentSpace) :
    infinitesimal_lift (R := R) (S := S) Q hQsq φ
        (SectionQuotient.generatorToInfinitesimal ((Generators.self R S).toExtension) l x) = 0 := by
  -- Specialize the generic cotangent-representative formula to the chosen summand element `l x`.
  rw [SectionQuotient.generatorToInfinitesimal_apply,
    SectionQuotient.generator_apply,
    infinitesimal_lift_apply_cotangent_representative
    (R := R) (S := S) Q hQsq φ (l x)]
  have hx : Extension.Cotangent.map φ (l x) = 0 := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hφ x
  rw [hx]
  have hz :
      (Q.kerCotangentEquiv hQsq).symm (0 : Q.Cotangent) = 0 := by
    simp
  rw [hz]
  rfl

/-- Helper for Lemma 10.149.1: generatorwise vanishing on the chosen section forces the entire
section-image ideal to lie in the kernel of the infinitesimal lift. -/
private lemma section_image_ideal_le_ker_of_generator_vanishing
    {A : Type*} [CommRing A] [Algebra R A]
    (l : ((Generators.self R S).toExtension).CotangentSpace →ₗ[S]
      ((Generators.self R S).toExtension).Cotangent)
    (φInf : ((Generators.self R S).toExtension.infinitesimal.Ring) →ₐ[R] A)
    (hzero : ∀ x : ((Generators.self R S).toExtension).CotangentSpace,
      φInf (SectionQuotient.generatorToInfinitesimal ((Generators.self R S).toExtension) l x) = 0) :
    SectionQuotient.ideal ((Generators.self R S).toExtension) l ≤ RingHom.ker φInf.toRingHom := by
  -- The source construction defines `J'` as the span of these explicit section generators.
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨x, rfl⟩
  simpa [RingHom.mem_ker] using hzero x

/-- Helper for Lemma 10.149.1: once the corrected infinitesimal lift kills the section-image
ideal, it factors through the quotient self-presentation `P/J'`. -/
private lemma factor_through_section_quotient_of_cotangent_vanish
    {A : Type*} [CommRing A] [Algebra R A]
    (I : Ideal A) (f : S →ₐ[R] A ⧸ I)
    (l : ((Generators.self R S).toExtension).CotangentSpace →ₗ[S]
      ((Generators.self R S).toExtension).Cotangent)
    (φInf : ((Generators.self R S).toExtension.infinitesimal.Ring) →ₐ[R] A)
    (hφInf : (Ideal.Quotient.mkₐ R I).comp φInf =
      f.comp (IsScalarTower.toAlgHom R ((Generators.self R S).toExtension.infinitesimal.Ring) S))
    (hzero : ∀ x : ((Generators.self R S).toExtension).CotangentSpace,
      φInf (SectionQuotient.generatorToInfinitesimal ((Generators.self R S).toExtension) l x) = 0) :
    ∃ g : (SectionQuotient.extension ((Generators.self R S).toExtension) l).Ring →ₐ[R] A,
      (Ideal.Quotient.mkₐ R I).comp g =
        f.comp (IsScalarTower.toAlgHom R (SectionQuotient.extension ((Generators.self R S).toExtension) l).Ring S) := by
  let Jbar := SectionQuotient.ideal ((Generators.self R S).toExtension) l
  have hker : Jbar ≤ RingHom.ker φInf.toRingHom :=
    section_image_ideal_le_ker_of_generator_vanishing
      (R := R) (S := S) (A := A) l φInf hzero
  have hquot :
      (IsScalarTower.toAlgHom R
          (SectionQuotient.extension ((Generators.self R S).toExtension) l).Ring S).comp
        (Ideal.Quotient.mkₐ R Jbar) =
        IsScalarTower.toAlgHom R ((Generators.self R S).toExtension.infinitesimal.Ring) S := by
    -- The quotient extension still reduces to the original infinitesimal self presentation.
    rw [SectionQuotient.extension_toAlgHom]
    exact Ideal.Quotient.liftₐ_comp (R₁ := R) (I := Jbar)
      (IsScalarTower.toAlgHom R ((Generators.self R S).toExtension.infinitesimal.Ring) S)
      (SectionQuotient.ideal_le_ker ((Generators.self R S).toExtension) l)
  refine ⟨Ideal.Quotient.liftₐ Jbar φInf hker, ?_⟩
  -- Compare the two candidate reductions after precomposing with the quotient map from `P0.inf/J'`.
  refine Ideal.Quotient.algHom_ext (R₁ := R) (I := Jbar) ?_
  calc
    (((Ideal.Quotient.mkₐ R I).comp (Ideal.Quotient.liftₐ Jbar φInf hker)).comp
        (Ideal.Quotient.mkₐ R Jbar)) =
        (Ideal.Quotient.mkₐ R I).comp φInf := by
          rw [AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp]
    _ = f.comp
        (IsScalarTower.toAlgHom R ((Generators.self R S).toExtension.infinitesimal.Ring) S) := hφInf
    _ =
        f.comp
          ((IsScalarTower.toAlgHom R
              (SectionQuotient.extension ((Generators.self R S).toExtension) l).Ring S).comp
            (Ideal.Quotient.mkₐ R Jbar)) := by
              rw [hquot]
    _ =
        (f.comp
          (IsScalarTower.toAlgHom R
            (SectionQuotient.extension ((Generators.self R S).toExtension) l).Ring S)).comp
          (Ideal.Quotient.mkₐ R Jbar) := by
            rw [← AlgHom.comp_assoc]

/-- Helper for Lemma 10.149.1: if the descended infinitesimal lift kills the section-image ideal,
then the owner cotangent obstruction already vanishes on the chosen section. -/
private lemma cotangent_vanish_of_section_image_ideal_le_ker
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    (Q : Extension R S') (hQsq : Q.ker ^ 2 = ⊥)
    (φ : ((Generators.self R S).toExtension).Hom Q)
    (l : ((Generators.self R S).toExtension).CotangentSpace →ₗ[S]
      ((Generators.self R S).toExtension).Cotangent)
    (hker : SectionQuotient.ideal ((Generators.self R S).toExtension) l ≤
      RingHom.ker (infinitesimal_lift (R := R) (S := S) Q hQsq φ).toRingHom) :
    (Extension.Cotangent.map φ) ∘ₗ l = 0 := by
  -- Each explicit generator of the section-image ideal already maps to zero under the descended
  -- infinitesimal lift, so the corresponding cotangent class vanishes as well.
  apply LinearMap.ext
  intro x
  have hgen :
      SectionQuotient.generatorToInfinitesimal ((Generators.self R S).toExtension) l x ∈
        SectionQuotient.ideal ((Generators.self R S).toExtension) l := by
    exact SectionQuotient.generator_mem ((Generators.self R S).toExtension) l x
  have hzero :
      infinitesimal_lift (R := R) (S := S) Q hQsq φ
          (SectionQuotient.generatorToInfinitesimal ((Generators.self R S).toExtension) l x) = 0 := by
    simpa [RingHom.mem_ker] using hker hgen
  rw [SectionQuotient.generatorToInfinitesimal_apply,
    SectionQuotient.generator_apply,
    infinitesimal_lift_apply_cotangent_representative
    (R := R) (S := S) Q hQsq φ (l x)] at hzero
  apply (Q.kerCotangentEquiv hQsq).symm.injective
  apply Subtype.ext
  simpa using hzero

/-- Helper for Lemma 10.149.1: once the owner homotopy difference vanishes, the two induced
infinitesimal lifts on `P/ker²` agree. -/
private lemma infinitesimal_lift_eq_of_sub_eq_zero
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    (Q : Extension R S') (hQsq : Q.ker ^ 2 = ⊥)
    (φ₁ φ₂ : ((Generators.self R S).toExtension).Hom Q)
    (hsub : φ₁.sub φ₂ = 0) :
    infinitesimal_lift (R := R) (S := S) Q hQsq φ₁ =
      infinitesimal_lift (R := R) (S := S) Q hQsq φ₂ := by
  let P0 : Extension R S := (Generators.self R S).toExtension
  have hAlg : φ₁.toAlgHom = φ₂.toAlgHom := by
    -- The vanishing homotopy forces the two owner maps to agree on the polynomial generators.
    apply MvPolynomial.algHom_ext
    intro s
    have hmk_zero :
        Extension.Cotangent.mk ((φ₁.subToKer φ₂) (MvPolynomial.X s)) = 0 := by
      have htmp := LinearMap.congr_fun hsub (1 ⊗ₜ .D _ _ (MvPolynomial.X s))
      rw [Extension.Hom.sub_one_tmul] at htmp
      simpa using htmp
    have hsubToKer_zero : ((φ₁.subToKer φ₂) (MvPolynomial.X s) : Q.ker) = 0 := by
      apply (Q.kerCotangentEquiv hQsq).injective
      simpa using hmk_zero
    have hsub_apply :
        φ₁.toAlgHom (MvPolynomial.X s) - φ₂.toAlgHom (MvPolynomial.X s) = 0 := by
      have hring_zero :
          (((φ₁.subToKer φ₂) (MvPolynomial.X s) : Q.ker) : Q.Ring) = 0 := by
        exact congrArg Subtype.val hsubToKer_zero
      change (((φ₁.subToKer φ₂) (MvPolynomial.X s) : Q.ker) : Q.Ring) = 0
      simpa [Extension.Hom.subToKer_apply_coe] using hring_zero
    exact sub_eq_zero.mp hsub_apply
  -- The quotient lift is determined by the owner map before modding out by `ker²`.
  refine Ideal.Quotient.algHom_ext (R₁ := R) <| AlgHom.ext fun x ↦ ?_
  rw [infinitesimal_lift, infinitesimal_lift]
  simpa [P0] using congrArg (fun ψ : P0.Ring →ₐ[R] Q.Ring ↦ ψ x) hAlg

/-- Helper for Lemma 10.149.1: two lifts out of the section quotient are equal once they induce
the same map modulo `I`. -/
private lemma factored_lift_unique
    {A : Type*} [CommRing A] [Algebra R A]
    (I : Ideal A)
    (f : S →ₐ[R] A ⧸ I)
    (l : ((Generators.self R S).toExtension).CotangentSpace →ₗ[S]
      ((Generators.self R S).toExtension).Cotangent)
    (hl : ((Generators.self R S).toExtension).cotangentComplex ∘ₗ l = LinearMap.id)
    (hI : I ^ 2 = ⊥)
    (g₁ g₂ : (SectionQuotient.extension ((Generators.self R S).toExtension) l).Ring →ₐ[R] A)
    (hg₁ : (Ideal.Quotient.mkₐ R I).comp g₁ =
      f.comp (IsScalarTower.toAlgHom R (SectionQuotient.extension ((Generators.self R S).toExtension) l).Ring S))
    (hg₂ : (Ideal.Quotient.mkₐ R I).comp g₂ =
      f.comp (IsScalarTower.toAlgHom R (SectionQuotient.extension ((Generators.self R S).toExtension) l).Ring S)) :
    g₁ = g₂ := by
  let P0 : Extension R S := (Generators.self R S).toExtension
  let Jbar := SectionQuotient.ideal ((Generators.self R S).toExtension) l
  -- Local instance justification (noncanonical choice): the `S`-algebra
  -- structure on `A ⧸ I` is determined by the explicit map `f`.
  let _ : Algebra S (A ⧸ I) := f.toAlgebra
  let Q : Extension R (A ⧸ I) := Ideal.Quotient.extension R I
  let φInf₁ : P0.infinitesimal.Ring →ₐ[R] A := g₁.comp (Ideal.Quotient.mkₐ R Jbar)
  let φInf₂ : P0.infinitesimal.Ring →ₐ[R] A := g₂.comp (Ideal.Quotient.mkₐ R Jbar)
  have hQsq : Q.ker ^ 2 = ⊥ := by
    simpa [Q] using Ideal.Quotient.extension_square_zero R I hI
  have hquot :
      (IsScalarTower.toAlgHom R
          (SectionQuotient.extension ((Generators.self R S).toExtension) l).Ring S).comp
        (Ideal.Quotient.mkₐ R Jbar) =
        IsScalarTower.toAlgHom R P0.infinitesimal.Ring S := by
    -- The section quotient still reduces to the infinitesimal self presentation before quotienting
    -- further by `Jbar`.
    rw [SectionQuotient.extension_toAlgHom]
    exact Ideal.Quotient.liftₐ_comp (R₁ := R) (I := Jbar)
      (IsScalarTower.toAlgHom R P0.infinitesimal.Ring S)
      (SectionQuotient.ideal_le_ker ((Generators.self R S).toExtension) l)
  have hφInf₁ :
      (Ideal.Quotient.mkₐ R I).comp φInf₁ =
        f.comp (IsScalarTower.toAlgHom R P0.infinitesimal.Ring S) := by
    -- Pull the reduction identity for `g₁` back across the quotient by `Jbar`.
    calc
      (Ideal.Quotient.mkₐ R I).comp φInf₁ =
          ((Ideal.Quotient.mkₐ R I).comp g₁).comp (Ideal.Quotient.mkₐ R Jbar) := by
            rfl
      _ =
          (f.comp
            (IsScalarTower.toAlgHom R
              (SectionQuotient.extension ((Generators.self R S).toExtension) l).Ring S)).comp
            (Ideal.Quotient.mkₐ R Jbar) := by rw [hg₁]
      _ =
          f.comp
            ((IsScalarTower.toAlgHom R
                (SectionQuotient.extension ((Generators.self R S).toExtension) l).Ring S).comp
              (Ideal.Quotient.mkₐ R Jbar)) := by
                rfl
      _ = f.comp (IsScalarTower.toAlgHom R P0.infinitesimal.Ring S) := by rw [hquot]
  have hφInf₂ :
      (Ideal.Quotient.mkₐ R I).comp φInf₂ =
        f.comp (IsScalarTower.toAlgHom R P0.infinitesimal.Ring S) := by
    -- The same reduction identity holds for the second quotient lift.
    calc
      (Ideal.Quotient.mkₐ R I).comp φInf₂ =
          ((Ideal.Quotient.mkₐ R I).comp g₂).comp (Ideal.Quotient.mkₐ R Jbar) := by
            rfl
      _ =
          (f.comp
            (IsScalarTower.toAlgHom R
              (SectionQuotient.extension ((Generators.self R S).toExtension) l).Ring S)).comp
            (Ideal.Quotient.mkₐ R Jbar) := by rw [hg₂]
      _ =
          f.comp
            ((IsScalarTower.toAlgHom R
                (SectionQuotient.extension ((Generators.self R S).toExtension) l).Ring S).comp
              (Ideal.Quotient.mkₐ R Jbar)) := by
                rfl
      _ = f.comp (IsScalarTower.toAlgHom R P0.infinitesimal.Ring S) := by rw [hquot]
  have hInfquot :
      (IsScalarTower.toAlgHom R P0.infinitesimal.Ring S).comp
        (Ideal.Quotient.mkₐ R (P0.ker ^ 2)) =
        IsScalarTower.toAlgHom R P0.Ring S := by
    -- Passing from `P0` to `P0/ker²` does not change the reduction to `S`.
    exact AlgHom.ext fun _ ↦ rfl
  let β₁ : P0.Ring →ₐ[R] A := φInf₁.comp (Ideal.Quotient.mkₐ R (P0.ker ^ 2))
  let β₂ : P0.Ring →ₐ[R] A := φInf₂.comp (Ideal.Quotient.mkₐ R (P0.ker ^ 2))
  have hβ₁ :
      (Ideal.Quotient.mkₐ R I).comp β₁ =
        f.comp (IsScalarTower.toAlgHom R P0.Ring S) := by
    -- Re-express the first quotient lift as a polynomial-owner lift.
    calc
      (Ideal.Quotient.mkₐ R I).comp β₁ =
          ((Ideal.Quotient.mkₐ R I).comp φInf₁).comp
            (Ideal.Quotient.mkₐ R (P0.ker ^ 2)) := by
              rfl
      _ =
          (f.comp (IsScalarTower.toAlgHom R P0.infinitesimal.Ring S)).comp
            (Ideal.Quotient.mkₐ R (P0.ker ^ 2)) := by rw [hφInf₁]
      _ =
          f.comp
            ((IsScalarTower.toAlgHom R P0.infinitesimal.Ring S).comp
              (Ideal.Quotient.mkₐ R (P0.ker ^ 2))) := by
                rfl
      _ = f.comp (IsScalarTower.toAlgHom R P0.Ring S) := by rw [hInfquot]
  have hβ₂ :
      (Ideal.Quotient.mkₐ R I).comp β₂ =
        f.comp (IsScalarTower.toAlgHom R P0.Ring S) := by
    -- The second quotient lift yields the same owner-level reduction.
    calc
      (Ideal.Quotient.mkₐ R I).comp β₂ =
          ((Ideal.Quotient.mkₐ R I).comp φInf₂).comp
            (Ideal.Quotient.mkₐ R (P0.ker ^ 2)) := by
              rfl
      _ =
          (f.comp (IsScalarTower.toAlgHom R P0.infinitesimal.Ring S)).comp
            (Ideal.Quotient.mkₐ R (P0.ker ^ 2)) := by rw [hφInf₂]
      _ =
          f.comp
            ((IsScalarTower.toAlgHom R P0.infinitesimal.Ring S).comp
              (Ideal.Quotient.mkₐ R (P0.ker ^ 2))) := by
                rfl
      _ = f.comp (IsScalarTower.toAlgHom R P0.Ring S) := by rw [hInfquot]
  obtain ⟨φ₁, hφ₁⟩ :=
    polynomial_lift_to_extension_hom
      (R := R) (S := S) I f β₁ hβ₁
  obtain ⟨φ₂, hφ₂⟩ :=
    polynomial_lift_to_extension_hom
      (R := R) (S := S) I f β₂ hβ₂
  have hφInf_eq₁ :
      infinitesimal_lift (R := R) (S := S) Q hQsq φ₁ = φInf₁ := by
    -- Both infinitesimal maps agree after precomposing with the quotient map from `P0.Ring`.
    refine Ideal.Quotient.algHom_ext (R₁ := R) <| AlgHom.ext fun x ↦ ?_
    rw [infinitesimal_lift]
    change φ₁.toAlgHom x = φInf₁ (Ideal.Quotient.mk (P0.ker ^ 2) x)
    rw [hφ₁]
    rfl
  have hφInf_eq₂ :
      infinitesimal_lift (R := R) (S := S) Q hQsq φ₂ = φInf₂ := by
    -- The same comparison identifies the second pulled-back owner with its infinitesimal lift.
    refine Ideal.Quotient.algHom_ext (R₁ := R) <| AlgHom.ext fun x ↦ ?_
    rw [infinitesimal_lift]
    change φ₂.toAlgHom x = φInf₂ (Ideal.Quotient.mk (P0.ker ^ 2) x)
    rw [hφ₂]
    rfl
  have hJbar₁ : Jbar ≤ RingHom.ker φInf₁.toRingHom := by
    -- Because `φInf₁` factors through the quotient by `Jbar`, it kills `Jbar` tautologically.
    intro y hy
    change g₁ (Ideal.Quotient.mk Jbar y) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy]
    exact map_zero g₁
  have hJbar₂ : Jbar ≤ RingHom.ker φInf₂.toRingHom := by
    -- The same tautological vanishing holds for `φInf₂`.
    intro y hy
    change g₂ (Ideal.Quotient.mk Jbar y) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy]
    exact map_zero g₂
  have hvanish₁ : (Extension.Cotangent.map φ₁) ∘ₗ l = 0 := by
    -- Reverse the quotient-kernel containment back into vanishing of the cotangent obstruction.
    have hker₁ :
        SectionQuotient.ideal ((Generators.self R S).toExtension) l ≤
          RingHom.ker (infinitesimal_lift (R := R) (S := S) Q hQsq φ₁).toRingHom := by
      intro y hy
      change infinitesimal_lift (R := R) (S := S) Q hQsq φ₁ y = 0
      rw [hφInf_eq₁]
      exact hJbar₁ <| by simpa [Jbar] using hy
    exact cotangent_vanish_of_section_image_ideal_le_ker
      (R := R) (S := S) Q hQsq φ₁ l hker₁
  have hvanish₂ : (Extension.Cotangent.map φ₂) ∘ₗ l = 0 := by
    -- The second owner lift has the same vanishing obstruction on the chosen section.
    have hker₂ :
        SectionQuotient.ideal ((Generators.self R S).toExtension) l ≤
          RingHom.ker (infinitesimal_lift (R := R) (S := S) Q hQsq φ₂).toRingHom := by
      intro y hy
      change infinitesimal_lift (R := R) (S := S) Q hQsq φ₂ y = 0
      rw [hφInf_eq₂]
      exact hJbar₂ <| by simpa [Jbar] using hy
    exact cotangent_vanish_of_section_image_ideal_le_ker
      (R := R) (S := S) Q hQsq φ₂ l hker₂
  have hsub_zero : φ₁.sub φ₂ = 0 := by
    -- Route correction: compare the two owner lifts only at the infinitesimal layer. The section
    -- `l` splits `P0.cotangentComplex`, so vanishing on `l` forces the homotopy difference to be
    -- zero everywhere.
    apply LinearMap.ext
    intro x
    have hsplit : P0.cotangentComplex (l x) = x := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hl x
    have hmap :
        Extension.Cotangent.map φ₁ (l x) - Extension.Cotangent.map φ₂ (l x) =
          φ₁.sub φ₂ (P0.cotangentComplex (l x)) := by
      simpa only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply, P0] using
        LinearMap.congr_fun (Extension.Cotangent.map_sub_map φ₁ φ₂) (l x)
    have hzero₁ : Extension.Cotangent.map φ₁ (l x) = 0 := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hvanish₁ x
    have hzero₂ : Extension.Cotangent.map φ₂ (l x) = 0 := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hvanish₂ x
    calc
      φ₁.sub φ₂ x = φ₁.sub φ₂ (P0.cotangentComplex (l x)) := by rw [hsplit]
      _ = Extension.Cotangent.map φ₁ (l x) - Extension.Cotangent.map φ₂ (l x) := by
            rw [← hmap]
      _ = 0 := by rw [hzero₁, hzero₂, sub_self]
  have hφInf :
      φInf₁ = φInf₂ := by
    -- Zero owner homotopy difference is exactly the input needed to compare the infinitesimal
    -- quotient lifts.
    rw [← hφInf_eq₁, ← hφInf_eq₂]
    exact infinitesimal_lift_eq_of_sub_eq_zero
      (R := R) (S := S) Q hQsq φ₁ φ₂ hsub_zero
  -- The quotient by `Jbar` is determined by its pullback to the infinitesimal self presentation.
  refine Ideal.Quotient.algHom_ext (R₁ := R) (I := Jbar) ?_
  change φInf₁ = φInf₂
  exact hφInf

private theorem existsUniversal_of_selfPresentation
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    [Algebra.FormallyUnramified R S] :
    ∃ P : Extension.{max u v} R S, FirstOrder.IsUniversal.{z} P := by
  -- Route correction: first stabilize the Stacks construction of the quotient extension cut out by
  -- a section of the cotangent complex; the remaining blocker is the owner-form lifting argument.
  obtain ⟨l, hl⟩ := cotangentComplex_has_section (R := R) (S := S)
  let P : Extension.{max u v} R S := SectionQuotient.extension ((Generators.self R S).toExtension) l
  have hsq : P.ker ^ 2 = ⊥ := by
    simpa [P] using SectionQuotient.extension_square_zero ((Generators.self R S).toExtension) l
  refine ⟨P, hsq, ?_⟩
  intro A _ _ I hI f
  obtain ⟨β, hβ⟩ :=
    exists_polynomial_lift
      (R := R) (S := S) (A := A) I hI f
  -- Local instance justification (noncanonical choice): the `S`-algebra
  -- structure on `A ⧸ I` is determined by the explicit map `f`.
  let _ : Algebra S (A ⧸ I) := f.toAlgebra
  let P0 : Extension R S := (Generators.self R S).toExtension
  let Q : Extension R (A ⧸ I) := Ideal.Quotient.extension R I
  obtain ⟨φ, rfl⟩ :=
    polynomial_lift_to_extension_hom
      (R := R) (S := S) I f β hβ
  have hQsq : Q.ker ^ 2 = ⊥ := by
    simpa [Q] using Ideal.Quotient.extension_square_zero R I hI
  obtain ⟨φu, hφu⟩ :=
    corrected_extension_hom_cotangent_vanish
      (R := R) (S := S) Q hQsq φ l hl
  let φInf := infinitesimal_lift (R := R) (S := S) Q hQsq φu
  have hφInf :
      (Ideal.Quotient.mkₐ R I).comp φInf =
        f.comp (IsScalarTower.toAlgHom R P0.infinitesimal.Ring S) := by
    -- The corrected owner map already descends through `P0.ker²`, so we can work on the
    -- infinitesimal self presentation before handling the section-image quotient.
    have hf : IsScalarTower.toAlgHom R S (A ⧸ I) = f := by
      ext
      rfl
    have h := infinitesimal_lift_comp_eq (R := R) (S := S) Q hQsq φu
    rw [Ideal.Quotient.extension_toAlgHom, hf] at h
    apply AlgHom.ext
    intro x
    exact DFunLike.congr_fun h x
  have hφInf_zero :
      ∀ x : P0.CotangentSpace,
        φInf (SectionQuotient.generatorToInfinitesimal P0 l x) = 0 := by
    -- The corrected owner map was chosen so that its cotangent obstruction vanishes on the chosen
    -- section, hence every explicit section generator already maps to zero.
    intro x
    exact section_generator_image_eq_zero_of_cotangent_vanish
      (R := R) (S := S) Q hQsq φu l hφu x
  obtain ⟨g, hg⟩ :=
    factor_through_section_quotient_of_cotangent_vanish
      (R := R) (S := S) (A := A) I f l φInf hφInf hφInf_zero
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  exact (factored_lift_unique
    (R := R) (S := S) (A := A) I f l hl hI g g' hg hg').symm

end Algebra.Extension.FirstOrder.SelfPresentation

namespace Algebra.Extension.FirstOrder

/-- Every formally unramified algebra admits a universal first-order
thickening.  The self-presentation used to construct it is hidden from the
consumer-facing statement. -/
@[stacks 04EB "existence of a universal first-order thickening"]
theorem existsUniversal
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    [Algebra.FormallyUnramified R S] :
    ∃ P : Extension.{max u v} R S, IsUniversal.{z} P :=
  SelfPresentation.existsUniversal_of_selfPresentation R S

end Algebra.Extension.FirstOrder
