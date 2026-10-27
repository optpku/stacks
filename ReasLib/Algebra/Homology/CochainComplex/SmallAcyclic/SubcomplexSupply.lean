/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.SmallAcyclic.Termwise
public import ReasLib.CategoryTheory.Abelian.SeparatorCoproduct.Refinement.Grothendieck
public import Mathlib.CategoryTheory.Generator.Preadditive
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-! # The termwise small acyclic subcomplex supply of Stacks 079K

The source size `|X|` is the cardinal of `Subobject X`. Starting from a generator map
`ψ : U ⟶ M.X n`, the construction takes its image in degree `n`, the image of `ψ ≫ d`
in degree `n + 1`, and zero in all higher degrees. Natural-number recursion constructs
successive lower terms: pull back the kernel of the preceding restricted differential,
then take the image of the bounded separator-coproduct map of Stacks 079J.

All choices below are native generator choices or conditional choices of individual
morphisms. No complex, refinement, or supply is chosen from an admitted existence theorem.
Compatibility, exactness, and cardinal estimates are separate propositions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe z w v u

namespace CochainComplex

namespace SmallAcyclic

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- Every nonzero acyclic complex is assigned an actual nonzero
subcomplex which is bounded above, acyclic, and termwise bounded by `kappa`. -/
@[stacks 079K "data-level small acyclic subcomplex supply"]
structure SubcomplexSupply (kappa : Cardinal.{z}) where
  /-- The assigned small acyclic subcomplex of a nonzero acyclic complex. -/
  sub : ∀ (Q : CochainComplex C ℤ), Q.Acyclic → ¬ IsZero Q → Subobject Q
  /-- The assigned subcomplex is nonzero. -/
  not_isZero (Q : CochainComplex C ℤ) (hQ : Q.Acyclic) (hne : ¬ IsZero Q) :
    ¬ IsZero (sub Q hQ hne : CochainComplex C ℤ)
  /-- The assigned subcomplex is bounded above, acyclic and termwise bounded by `kappa`. -/
  boundedBy (Q : CochainComplex C ℤ) (hQ : Q.Acyclic) (hne : ¬ IsZero Q) :
    BoundedBy kappa (sub Q hQ hne : CochainComplex C ℤ)

variable {C}

/-- Enlarge the cardinal bound of a supply, keeping its assigned subcomplexes. -/
def SubcomplexSupply.enlarge {kappa lambda : Cardinal.{z}}
    (S : SubcomplexSupply C kappa) (h : kappa ≤ lambda) : SubcomplexSupply C lambda where
  sub := S.sub
  not_isZero := S.not_isZero
  boundedBy Q hQ hne := (S.boundedBy Q hQ hne).mono h

@[simp]
lemma SubcomplexSupply.enlarge_sub {kappa lambda : Cardinal.{z}}
    (S : SubcomplexSupply C kappa) (h : kappa ≤ lambda)
    (Q : CochainComplex C ℤ) (hQ : Q.Acyclic) (hne : ¬ IsZero Q) :
    (S.enlarge h).sub Q hQ hne = S.sub Q hQ hne := rfl

/-- A data-level supply witnesses the uniform subcomplex bound. -/
theorem SubcomplexSupply.hasSubcomplexes {kappa : Cardinal.{z}}
    (S : SubcomplexSupply C kappa) : HasSubcomplexes C kappa :=
  fun Q hQ hne ↦ ⟨S.sub Q hQ hne, S.not_isZero Q hQ hne, S.boundedBy Q hQ hne⟩

end SmallAcyclic

namespace SmallAcyclic.Grothendieck

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- The small-universe version of `c(κ) = |∐ κ U|`, so it can be iterated. -/
@[stacks 079J "iterable source cardinal"]
def growth (U : C) (κ : Cardinal.{w}) : Cardinal.{w} :=
  Subobject.smallCardinal (∐ fun _ : κ.out ↦ U)

/-- The source's uniform cardinal `sup {c^r(|U|) | r ≥ 1}`. -/
@[stacks 079K "source uniform cardinal"]
def bound (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C] :
    Cardinal.{w} :=
  ⨆ r : ℕ, (growth (separator C))^[r + 1] (Subobject.smallCardinal (separator C))

/-- A nonzero complex has a nonzero map from the generator in some degree.
This fully proved statement is the only existence statement used to select the seed. -/
theorem exists_nonzero_generator_map {U : C} (hU : IsSeparator U)
    (M : CochainComplex C ℤ) (hne : ¬ IsZero M) :
    ∃ n : ℤ, ∃ ψ : U ⟶ M.X n, ψ ≠ 0 := by
  classical
  by_contra! h
  apply hne
  apply (IsZero.iff_id_eq_zero M).2
  ext i
  exact hU.def _ _ (fun f ↦ by simp [h i f])

/-- The chosen nonzero source degree; the existence proof is fully proved above. -/
def seedDegree {U : C} (hU : IsSeparator U) (M : CochainComplex C ℤ)
    (hne : ¬ IsZero M) : ℤ :=
  (exists_nonzero_generator_map hU M hne).choose

/-- The chosen generator map in the seed degree. -/
def seedMap {U : C} (hU : IsSeparator U) (M : CochainComplex C ℤ)
    (hne : ¬ IsZero M) : U ⟶ M.X (seedDegree hU M hne) :=
  (exists_nonzero_generator_map hU M hne).choose_spec.choose

theorem seedMap_ne_zero {U : C} (hU : IsSeparator U) (M : CochainComplex C ℤ)
    (hne : ¬ IsZero M) : seedMap hU M hne ≠ 0 :=
  (exists_nonzero_generator_map hU M hne).choose_spec.choose_spec

/-- A specified separator-test map, choosing an individual witness only when one exists.
The top subobject, and any index with no avoiding map, gives zero. The data do not depend
on a proof that `π` is epic or on `SeparatorEpi.Family.nonempty`. -/
def testMap (U : C) {A B : C} (π : A ⟶ B)
    (i : Shrink.{w} (Subobject B)) : U ⟶ A :=
  open Classical in
  if h : ∃ f : U ⟶ A, ¬ (SeparatorEpi.subobjectAt i).Factors (f ≫ π) then h.choose else 0

/-- The actual 079J coproduct map. -/
def refinementMap (U : C) {A B : C} (π : A ⟶ B) :
    (∐ fun _ : Shrink.{w} (Subobject B) ↦ U) ⟶ A :=
  Sigma.desc (testMap U π)

/-- The actual bounded-size refinement is the image of the separator coproduct map. -/
@[stacks 079J "specified bounded refinement"]
def refinement (U : C) {A B : C} (π : A ⟶ B) : Subobject A :=
  imageSubobject (refinementMap U π)

/-- For an epimorphism the test maps form the existing 079J family. -/
def epiFamily {U : C} (hU : IsSeparator U) {A B : C} (π : A ⟶ B) [Epi π] :
    SeparatorEpi.Family U π where
  component := testMap U π
  component_eq_zero := by
    intro i hi
    classical
    simp only [testMap]
    split_ifs with h
    · have ht : ∀ f : U ⟶ A, (SeparatorEpi.subobjectAt i).Factors (f ≫ π) := by
        intro f
        rw [hi]
        exact Subobject.top_factors _
      exact False.elim (h.choose_spec (ht _))
    · rfl
  not_factors := sorry

/-- The specified refinement agrees with the reusable 079J image construction. -/
theorem refinement_eq {U : C} (hU : IsSeparator U) {A B : C} (π : A ⟶ B) [Epi π] :
    refinement U π = (epiFamily hU π).refinement := rfl

/-- A refinement of an epimorphism still surjects onto the target. -/
theorem refinement_epi {U : C} (hU : IsSeparator U) {A B : C} (π : A ⟶ B) [Epi π] :
    Epi ((refinement U π).arrow ≫ π) := sorry

/-- The 079J bound, in the universe in which the cardinal is iterated. -/
theorem refinement_cardinal {U : C} (hU : IsSeparator U) {A B : C} (π : A ⟶ B) [Epi π] :
    Subobject.smallCardinal (refinement U π : C) ≤ growth U (Subobject.smallCardinal B) := sorry

/-- One downward term, with the actual outgoing differential. The target is retained as
an object, avoiding transport of the previously constructed term in the recursion. -/
structure DownTerm (M : CochainComplex C ℤ) (k : ℤ) where
  sub : Subobject (M.X k)
  target : C
  d : (sub : C) ⟶ target

/-- The inverse image of the preceding kernel, with its native pullback projections. -/
def inverseImage {M : CochainComplex C ℤ} {k : ℤ} (T : DownTerm M k) : C :=
  pullback (M.d (k - 1) k) (kernel.ι T.d ≫ T.sub.arrow)

/-- The native pullback projection to the preceding kernel. At recursive terms of an
acyclic source it is epic, as recorded by `descend_inverseImage_epi`. -/
def inverseImageπ {M : CochainComplex C ℤ} {k : ℤ} (T : DownTerm M k) :
    inverseImage T ⟶ kernel T.d :=
  pullback.snd _ _

/-- Its inclusion into the next lower term of the ambient complex. -/
def inverseImageι {M : CochainComplex C ℤ} {k : ℤ} (T : DownTerm M k) :
    inverseImage T ⟶ M.X (k - 1) :=
  pullback.fst _ _

/-- This inclusion is monic because the other leg is a composite of kernel and subobject
inclusions. The proof uses only native pullback instances. -/
instance mono_inverseImageι {M : CochainComplex C ℤ} {k : ℤ} (T : DownTerm M k) :
    Mono (inverseImageι T) := by
  haveI : Mono (kernel.ι T.d ≫ T.sub.arrow) := inferInstance
  exact pullback.fst_of_mono (f := M.d (k - 1) k) (g := kernel.ι T.d ≫ T.sub.arrow)

/-- One descending 079K step: the image refinement inside the inverse image is embedded
in `M.X (k - 1)`, and its differential is the actual projection to the old kernel. -/
@[stacks 079K "descending kernel preimage step"]
def lower (U : C) {M : CochainComplex C ℤ} {k : ℤ} (T : DownTerm M k) :
    DownTerm M (k - 1) :=
  let P := refinement U (inverseImageπ T)
  let f := P.arrow ≫ inverseImageι T
  { sub := Subobject.mk f
    target := (T.sub : C)
    d := (Subobject.underlyingIso f).hom ≫ P.arrow ≫ inverseImageπ T ≫ kernel.ι T.d }

/-- The initial differential from `image ψ` to `image (ψ ≫ d)` satisfies the
cokernel equation needed by the native `Abelian.monoLift`. -/
theorem initial_condition {U : C} (M : CochainComplex C ℤ) (n : ℤ) (ψ : U ⟶ M.X n) :
    ((imageSubobject ψ).arrow ≫ M.d n (n + 1)) ≫
      cokernel.π (imageSubobject (ψ ≫ M.d n (n + 1))).arrow = 0 := by
  apply (cancel_epi (factorThruImageSubobject ψ)).1
  simp only [← Category.assoc, imageSubobject_arrow_comp, comp_zero]
  calc
    (ψ ≫ M.d n (n + 1)) ≫ cokernel.π (imageSubobject (ψ ≫ M.d n (n + 1))).arrow =
        factorThruImageSubobject (ψ ≫ M.d n (n + 1)) ≫
          (imageSubobject (ψ ≫ M.d n (n + 1))).arrow ≫
            cokernel.π (imageSubobject (ψ ≫ M.d n (n + 1))).arrow := by
              simp only [← Category.assoc, imageSubobject_arrow_comp]
    _ = 0 := by simp

/-- The source's initial two image terms and their restricted differential. -/
def initial {U : C} (M : CochainComplex C ℤ) (n : ℤ) (ψ : U ⟶ M.X n) : DownTerm M n where
  sub := imageSubobject ψ
  target := (imageSubobject (ψ ≫ M.d n (n + 1)) : C)
  d := Abelian.monoLift (imageSubobject (ψ ≫ M.d n (n + 1))).arrow
    ((imageSubobject ψ).arrow ≫ M.d n (n + 1)) (initial_condition M n ψ)

/-- Recursive degrees descend one integer at each natural-number step. -/
def degree (n : ℤ) : ℕ → ℤ
  | 0 => n
  | r + 1 => degree n r - 1

theorem degree_eq (n : ℤ) (r : ℕ) : degree n r = n - (r : ℤ) := by
  induction r with
  | zero => simp [degree]
  | succ r hr => simp only [degree, hr, Nat.cast_add, Nat.cast_one]; omega

/-- Actual descending termwise recursion, beginning at `image ψ`. -/
def descend {U : C} (M : CochainComplex C ℤ) (n : ℤ) (ψ : U ⟶ M.X n) :
    (r : ℕ) → DownTerm M (degree n r)
  | 0 => initial M n ψ
  | r + 1 => lower U (descend M n ψ r)

/-- Acyclicity makes the inverse-image projection in each actual recursive step epic. -/
theorem descend_inverseImage_epi {U : C} (hU : IsSeparator U) (M : CochainComplex C ℤ)
    (hM : M.Acyclic) (n : ℤ) (ψ : U ⟶ M.X n) (r : ℕ) :
    Epi (inverseImageπ (descend M n ψ r)) := sorry

/-- After `r` downward steps the size is at most `c^r(|U|)`. -/
theorem descend_cardinal {U : C} (hU : IsSeparator U) (M : CochainComplex C ℤ)
    (hM : M.Acyclic) (n : ℤ) (ψ : U ⟶ M.X n) (r : ℕ) :
    Subobject.smallCardinal ((descend M n ψ r).sub : C) ≤
      (growth U)^[r] (Subobject.smallCardinal U) := sorry

/-- The chosen subobject in every degree: descending terms, the upper image, then zero. -/
def term {U : C} (M : CochainComplex C ℤ) (n : ℤ) (ψ : U ⟶ M.X n) (i : ℤ) :
    Subobject (M.X i) :=
  open Classical in
  if hi : i ≤ n then
    let e : degree n (n - i).toNat = i := by rw [degree_eq]; omega
    e ▸ (descend M n ψ (n - i).toNat).sub
  else if hi : i = n + 1 then
    hi.symm ▸ imageSubobject (ψ ≫ M.d n (n + 1))
  else ⊥

/-- The termwise inclusions are closed under the ambient differential. This is an equation,
not an existential factorization from which a morphism is chosen. -/
theorem term_condition {U : C} (M : CochainComplex C ℤ) (n : ℤ) (ψ : U ⟶ M.X n)
    (i j : ℤ) :
    ((term M n ψ i).arrow ≫ M.d i j) ≫ cokernel.π (term M n ψ j).arrow = 0 := sorry

/-- The full termwise subcomplex, with native kernel lifts for all restricted differentials. -/
@[stacks 079K "actual termwise subcomplex"]
def termwise {U : C} (M : CochainComplex C ℤ) (n : ℤ) (ψ : U ⟶ M.X n) :
    HomologicalComplex.TermwiseSubcomplex M where
  X := term M n ψ
  d i j := Abelian.monoLift (term M n ψ j).arrow
    ((term M n ψ i).arrow ≫ M.d i j) (term_condition M n ψ i j)
  comm _ _ := (Abelian.monoLift_comp _ _ _).symm

/-- All terms strictly above `n + 1` are zero by construction. -/
theorem term_eq_bot {U : C} (M : CochainComplex C ℤ) (n : ℤ) (ψ : U ⟶ M.X n)
    (i : ℤ) (hi : n + 1 < i) : term M n ψ i = ⊥ := by
  simp [term, show ¬ i ≤ n by omega, show i ≠ n + 1 by omega]

/-- Bounded-above support is literal zero support above the upper image. -/
theorem termwise_isZero {U : C} (M : CochainComplex C ℤ) (n : ℤ) (ψ : U ⟶ M.X n)
    (i : ℤ) (hi : n + 1 < i) : IsZero ((termwise M n ψ).X i : C) := by
  change IsZero (term M n ψ i : C)
  rw [term_eq_bot M n ψ i hi]
  exact (isZero_zero C).of_iso Subobject.botCoeIsoZero

/-- Acyclicity of the source supplies exactness at every recursively constructed term. -/
theorem termwise_exact {U : C} (hU : IsSeparator U) (M : CochainComplex C ℤ)
    (hM : M.Acyclic) (n : ℤ) (ψ : U ⟶ M.X n) (i : ℤ) :
    imageSubobject ((termwise M n ψ).d (i - 1) i) =
      kernelSubobject ((termwise M n ψ).d i (i + 1)) := sorry

/-- The uniform cardinal controls every term, as in the descending induction of 079K. -/
theorem termwise_cardinal (M : CochainComplex C ℤ) (hM : M.Acyclic)
    (n : ℤ) (ψ : separator C ⟶ M.X n) (i : ℤ) :
    Cardinal.lift.{w, max u v} (Cardinal.mk (Subobject ((termwise M n ψ).X i : C))) ≤
      Cardinal.lift.{max u v, w} (bound C) := sorry

/-- The constructed subcomplex is bounded above, acyclic, and uniformly small. -/
theorem termwise_boundedBy (M : CochainComplex C ℤ) (hM : M.Acyclic)
    (n : ℤ) (ψ : separator C ⟶ M.X n) : BoundedBy (bound C) (termwise M n ψ).complex := by
  refine ⟨⟨n + 1, ?_⟩, ?_, termwise_cardinal M hM n ψ⟩
  · exact (CochainComplex.isStrictlyLE_iff _ _).2 (termwise_isZero M n ψ)
  · exact (HomologicalComplex.TermwiseSubcomplex.acyclic_iff_image_eq_kernel _).2
      (termwise_exact (isSeparator_separator C) M hM n ψ)

/-- The seed factors through the constructed degree `n`. -/
theorem seed_factors {U : C} (M : CochainComplex C ℤ) (n : ℤ) (ψ : U ⟶ M.X n) :
    (term M n ψ n).Factors ψ := sorry

/-- The subcomplex supplied to the reduction tower; only the seed map and degree are chosen. -/
def subcomplex (M : CochainComplex C ℤ) (hne : ¬ IsZero M) : Subobject M :=
  (termwise M (seedDegree (isSeparator_separator C) M hne)
    (seedMap (isSeparator_separator C) M hne)).toSubobject

/-- A nonzero seed makes the constructed subcomplex nonzero. -/
theorem subcomplex_not_isZero (M : CochainComplex C ℤ) (hne : ¬ IsZero M) :
    ¬ IsZero (subcomplex M hne : CochainComplex C ℤ) := sorry

theorem subcomplex_boundedBy (M : CochainComplex C ℤ) (hM : M.Acyclic) (hne : ¬ IsZero M) :
    BoundedBy (bound C) (subcomplex M hne : CochainComplex C ℤ) :=
  (termwise_boundedBy M hM _ _).of_iso
    (termwise M (seedDegree (isSeparator_separator C) M hne)
      (seedMap (isSeparator_separator C) M hne)).underlyingIso.symm

/-- Ambient-category producer of the actual 079K (1) supply. -/
@[stacks 079K "Grothendieck subcomplex supply"]
def subcomplexSupply (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C] :
    SubcomplexSupply C (bound C) where
  sub M _ hne := subcomplex M hne
  not_isZero M _ hne := subcomplex_not_isZero M hne
  boundedBy M hM hne := subcomplex_boundedBy M hM hne

end SmallAcyclic.Grothendieck

end CochainComplex
