module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.Presentable.StrongGenerator
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Comma.CardinalArrow
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finitely presented bundled modules

This file packages `Module.FinitePresentation` as an object property of `ModuleCat`.  The
property, its isomorphism invariance, and its filtered-colimit generation theorem are independent
of sheaves and textbook chapters.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v

namespace ModuleCat

variable (R : Type u) [Ring R]

noncomputable section

-- Local instance justification (proof-local temporary data): filtered-colimit presentability
-- arguments below require regularity of `Cardinal.aleph0`.
attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- The object property of a bundled `R`-module being finitely presented. -/
@[stacks 00HA "finitely presented module property"]
abbrev isFinitePresentation : ObjectProperty (ModuleCat.{v} R) :=
  fun M => Module.FinitePresentation R M

/-- Membership in `ModuleCat.isFinitePresentation` is ordinary finite presentation of the
underlying module. -/
@[simp]
theorem isFinitePresentation_iff (M : ModuleCat.{v} R) :
    isFinitePresentation.{u, v} R M ↔ Module.FinitePresentation R M := Iff.rfl

/-- Finite presentation of bundled modules is invariant under isomorphism. -/
@[stacks 00HA "isomorphism closure"]
instance isFinitePresentation.isClosedUnderIsomorphisms :
    (isFinitePresentation.{u, v} R).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    -- Local instance justification (proof-local temporary data): the object-property hypothesis
    -- supplies finite presentation to the equivalence theorem.
    letI : Module.FinitePresentation R X := hX
    exact Module.FinitePresentation.of_equiv e.toLinearEquiv

namespace isFinitePresentation

/-- The zero module is finitely presented. -/
instance containsZero : (isFinitePresentation.{u, v} R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _, by
    change Module.FinitePresentation R PUnit
    infer_instance⟩

/-- Finitely presented modules are closed under finite coproducts. -/
instance isClosedUnderFiniteCoproducts :
    ObjectProperty.IsClosedUnderFiniteCoproducts (isFinitePresentation.{u, v} R) where
  isClosedUnderColimitsOfShape J := by
    intro
    constructor
    rintro Z ⟨p⟩
    let f := fun j : J ↦ p.diag.obj ⟨j⟩
    -- Local instance justification (proof-local temporary data): each object of the finite
    -- diagram is finitely presented when forming its product.
    letI (j : J) : Module.FinitePresentation R (f j) := p.prop_diag_obj ⟨j⟩
    have hpi : isFinitePresentation R (ModuleCat.of R (∀ j, f j)) := by
      change Module.FinitePresentation R (∀ j, f j)
      infer_instance
    have hcoprod : isFinitePresentation R (∐ f) :=
      (isFinitePresentation R).prop_of_iso
        ((ModuleCat.biproductIsoPi f).symm ≪≫ biproduct.isoCoproduct f) hpi
    have hcolimit : isFinitePresentation R (colimit p.diag) :=
      (isFinitePresentation R).prop_of_iso (Sigma.isoColimit p.diag) hcoprod
    exact (isFinitePresentation R).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit p.diag) p.isColimit) hcolimit

/-- The cokernel of a map from a finite module to a finitely presented module is finitely
presented. -/
theorem cokernel_of_finite {M N : ModuleCat.{v} R} (f : M ⟶ N)
    (hM : Module.Finite R M) (hN : isFinitePresentation R N) :
    isFinitePresentation R (cokernel f) := by
  -- Local instance justification (proof-local temporary data): the explicit finiteness
  -- hypothesis is needed by the finite-generation result for the range.
  letI : Module.Finite R M := hM
  -- Local instance justification (proof-local temporary data): the explicit presentation
  -- hypothesis is needed by the quotient finite-presentation theorem.
  letI : Module.FinitePresentation R N := hN
  have hrange : f.hom.range.FG := Submodule.fg_range f.hom
  have hquot : Module.FinitePresentation R (N ⧸ f.hom.range) :=
    Module.finitePresentation_of_surjective f.hom.range.mkQ
      (Submodule.mkQ_surjective _) (by
        simpa only [Submodule.ker_mkQ] using hrange)
  -- Local instance justification (proof-local temporary data): the quotient presentation is
  -- transported across the cokernel equivalence in the next step.
  letI : Module.FinitePresentation R (N ⧸ f.hom.range) := hquot
  exact Module.FinitePresentation.of_equiv
    (ModuleCat.cokernelIsoRangeQuotient f).symm.toLinearEquiv

/-- Finitely presented modules are closed under cokernels. -/
instance isClosedUnderCokernels :
    ObjectProperty.IsClosedUnderCokernels (isFinitePresentation.{u, v} R) where
  cokernels_le := by
    rintro Z ⟨f, k, hk, ⟨hX, hY⟩⟩
    -- Local instance justification (proof-local temporary data): finite presentation of the
    -- source supplies the finite-module instance required by `cokernel_of_finite`.
    letI : Module.FinitePresentation R _ := hX
    have hc : isFinitePresentation R (cokernel f) :=
      cokernel_of_finite (R := R) f (by infer_instance) hY
    exact (isFinitePresentation R).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk) hc

end isFinitePresentation

private noncomputable instance preservesColimit_forget
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{max u v} R) :
    PreservesColimit F (forget (ModuleCat.{max u v} R)) :=
  preservesColimit_of_preserves_colimit_cocone
    (ModuleCat.FilteredColimits.colimitCoconeIsColimit F)
    (Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget (ModuleCat.{max u v} R)))

/-! The next two module-specific compactness lemmas allow the filtered index and the module
carriers to live in their natural different universes. -/

/-- A map from a finitely presented module into a filtered colimit factors through one stage. -/
theorem finitePresentation_exists_factor
    {J : Type v} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ ModuleCat.{max u v} R} {c : Cocone F} (hc : IsColimit c)
    {P : ModuleCat.{max u v} R} [Module.FinitePresentation R P]
    (f : P ⟶ c.pt) :
    ∃ (j : J) (g : P ⟶ F.obj j), g ≫ c.ι.app j = f := by
  let hc' := isColimitOfPreserves (forget (ModuleCat.{max u v} R)) hc
  obtain ⟨s, hs, hK⟩ := (inferInstance : Module.FinitePresentation R P)
  let q : (s →₀ R) →ₗ[R] P := Finsupp.linearCombination R Subtype.val
  have hq : Function.Surjective q := by
    rw [← LinearMap.range_eq_top]
    change LinearMap.range (Finsupp.linearCombination R Subtype.val) = ⊤
    rw [Finsupp.range_linearCombination, Subtype.range_coe_subtype]
    exact hs
  choose j y hy using fun x : s ↦
    Types.jointly_surjective_of_isColimit hc' (f x)
  let d : Cocone (Discrete.functor j) := IsFiltered.cocone (Discrete.functor j)
  let z : s → F.obj d.pt := fun x ↦ F.map (d.ι.app ⟨x⟩) (y x)
  let g₀ : (s →₀ R) →ₗ[R] F.obj d.pt := Finsupp.linearCombination R z
  have hg₀ : (c.ι.app d.pt).hom.comp g₀ = f.hom.comp q := by
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    change c.ι.app d.pt (g₀ (Finsupp.single x 1)) = f (q (Finsupp.single x 1))
    simp only [g₀, q, z, Finsupp.linearCombination_single, one_smul]
    calc
      _ = c.ι.app (j x) (y x) := by
        simpa only [ModuleCat.comp_apply] using!
          ConcreteCategory.congr_hom (c.w (d.ι.app ⟨x⟩)) (y x)
      _ = _ := hy x
  obtain ⟨t, ht⟩ := hK
  have hzero (r : t) : c.ι.app d.pt (g₀ r) = 0 := by
    have hr : (r : s →₀ R) ∈ LinearMap.ker q := by
      rw [← ht]
      exact Submodule.subset_span r.property
    have h : c.ι.app d.pt (g₀ r) = f (q r) := by
      exact LinearMap.congr_fun hg₀ r
    rw [LinearMap.mem_ker.mp hr, map_zero] at h
    exact h
  choose k a ha using fun r : t ↦
    (Types.FilteredColimit.isColimit_eq_iff' hc' (g₀ r) (0 : F.obj d.pt)).mp (by
      change c.ι.app d.pt (g₀ r) = c.ι.app d.pt 0
      simpa using hzero r)
  obtain ⟨l, b, a', hba⟩ := IsFiltered.wideSpan a
  let g₁ : (s →₀ R) →ₗ[R] F.obj l := (F.map b).hom.comp g₀
  have hker : LinearMap.ker q ≤ LinearMap.ker g₁ := by
    have htq : Submodule.span R (t : Set (s →₀ R)) = LinearMap.ker q := by
      simpa [q] using ht
    rw [← htq]
    refine Submodule.span_le.2 ?_
    intro r hr
    change g₁ r = 0
    change F.map b (g₀ r) = 0
    let rr : t := ⟨r, hr⟩
    rw [← hba rr, F.map_comp]
    change F.map (a' rr) (F.map (a rr) (g₀ r)) = 0
    have har : F.map (a rr) (g₀ r) = 0 := by
      have har' := ha rr
      change F.map (a rr) (g₀ r) = F.map (a rr) 0 at har'
      simpa using har'
    rw [har, map_zero]
  let lift : (s →₀ R) ⧸ LinearMap.ker q →ₗ[R] F.obj l :=
    (LinearMap.ker q).liftQ g₁ hker
  let e : ((s →₀ R) ⧸ LinearMap.ker q) ≃ₗ[R] P :=
    q.quotKerEquivOfSurjective hq
  let g : P →ₗ[R] F.obj l := lift.comp e.symm.toLinearMap
  refine ⟨l, ModuleCat.ofHom g, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := hq x
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, g, e,
    LinearEquiv.coe_toLinearMap, LinearMap.quotKerEquivOfSurjective_symm_apply,
    lift, Submodule.liftQ_apply]
  have hx := LinearMap.congr_fun hg₀ x
  exact (ConcreteCategory.congr_hom (c.w b) (g₀ x)).trans hx

/-- Two maps from a finitely presented module that agree in a filtered colimit agree after a
common later stage. -/
theorem finitePresentation_exists_eq
    {J : Type v} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ ModuleCat.{max u v} R} {c : Cocone F} (hc : IsColimit c)
    {P : ModuleCat.{max u v} R} [Module.FinitePresentation R P]
    {j : J} (f g : P ⟶ F.obj j)
    (h : f ≫ c.ι.app j = g ≫ c.ι.app j) :
    ∃ (k : J) (a : j ⟶ k), f ≫ F.map a = g ≫ F.map a := by
  let hc' := isColimitOfPreserves (forget (ModuleCat.{max u v} R)) hc
  obtain ⟨s, hs, _⟩ := (inferInstance : Module.FinitePresentation R P)
  have hx (x : s) : c.ι.app j (f x) = c.ι.app j (g x) :=
    ConcreteCategory.congr_hom h x
  choose k a ha using fun x : s ↦
    (Types.FilteredColimit.isColimit_eq_iff' hc' (f x) (g x)).mp (hx x)
  obtain ⟨l, b, a', hba⟩ := IsFiltered.wideSpan a
  refine ⟨l, b, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext_on hs
  intro x hx'
  let xx : s := ⟨x, hx'⟩
  change F.map b (f x) = F.map b (g x)
  rw [← hba xx, F.map_comp]
  change F.map (a' xx) (F.map (a xx) (f x)) =
    F.map (a' xx) (F.map (a xx) (g x))
  exact congr_arg (F.map (a' xx)) (ha xx)

/-- A finitely presented module is finitely presentable as an object of `ModuleCat` in the
canonical universe containing both the ring and module carriers. -/
@[stacks 00HA "categorical finite presentability"]
instance isFinitelyPresentable_of_finitePresentation (P : ModuleCat.{max u v} R)
    [Module.FinitePresentation R P] :
    CategoryTheory.IsFinitelyPresentable.{max u v} P := by
  rw [CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
  refine ⟨fun J _ _ ↦ ⟨?_⟩⟩
  intro F
  refine ⟨fun {c} hc ↦ ⟨?_⟩⟩
  apply Types.FilteredColimit.isColimitOf'
  · intro f
    obtain ⟨j, g, hg⟩ := finitePresentation_exists_factor R hc f
    exact ⟨j, g, hg.symm⟩
  · intro j f g h
    obtain ⟨k, a, ha⟩ := finitePresentation_exists_eq R hc f g h
    exact ⟨k, a, ha⟩

/-- Explicit bridge from module finite presentation to categorical finite presentability. This
form consumes an existing hypothesis without installing a proof-local instance. -/
@[stacks 00HA "explicit categorical finite presentability"]
theorem _root_.Module.FinitePresentation.isFinitelyPresentable
    {P : ModuleCat.{max u v} R} (hP : Module.FinitePresentation R P) :
    CategoryTheory.IsFinitelyPresentable.{max u v} P := by
  -- Local instance justification (proof-local temporary data): the explicit module hypothesis
  -- is consumed by the canonical categorical presentability instance.
  letI := hP
  infer_instance

private noncomputable instance finitePresentationFullSubcategoryHasCoequalizers :
    HasCoequalizers (isFinitePresentation.{u, max u v} R).FullSubcategory :=
  Preadditive.hasCoequalizers_of_hasCokernels

private noncomputable instance finitePresentationFullSubcategoryHasFiniteBiproducts :
    HasFiniteBiproducts (isFinitePresentation.{u, max u v} R).FullSubcategory :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

private noncomputable instance finitePresentationFullSubcategoryHasBinaryBiproducts :
    HasBinaryBiproducts (isFinitePresentation.{u, max u v} R).FullSubcategory :=
  hasBinaryBiproducts_of_finite_biproducts _

private noncomputable instance finitePresentationFullSubcategoryHasFiniteColimits :
    HasFiniteColimits (isFinitePresentation.{u, max u v} R).FullSubcategory :=
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

private noncomputable instance finitePresentationInclusionPreservesFiniteColimits :
    PreservesFiniteColimits (isFinitePresentation.{u, max u v} R).ι := by
  -- Local instance justification (proof-local temporary data): preservation of each cokernel
  -- is installed only to derive preservation of finite colimits for this inclusion.
  letI preservesCokernel
      {X Y : (isFinitePresentation.{u, max u v} R).FullSubcategory} (f : X ⟶ Y) :
      PreservesColimit (parallelPair f 0) (isFinitePresentation.{u, max u v} R).ι :=
    (isFinitePresentation.{u, max u v} R).preservesCokernels_ι f
  exact Functor.preservesFiniteColimits_of_preservesCokernels
    (isFinitePresentation.{u, max u v} R).ι

private lemma isFinitePresentation_closedUnderFiniteColimits
    (J : Type (max u v)) [SmallCategory J] [FinCategory J] :
    (isFinitePresentation.{u, max u v} R).IsClosedUnderColimitsOfShape J := by
  apply ObjectProperty.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι

private lemma rankOneStrongGenerator :
    (ObjectProperty.singleton
      (ModuleCat.of R (Shrink.{max u v} R) : ModuleCat.{max u v} R)).IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨?_, ?_⟩
  · exact ModuleCat.isSeparator R
  · intro X Y i _ hi
    have hsurj : Function.Surjective i := by
      intro y
      let e : Shrink.{max u v} R ≃ₗ[R] R := Shrink.linearEquiv.{max u v} R R
      let f : (ModuleCat.of R (Shrink.{max u v} R) : ModuleCat.{max u v} R) ⟶ Y :=
        ModuleCat.ofHom ((LinearMap.toSpanSingleton R Y y).comp e.toLinearMap)
      obtain ⟨g, hg⟩ := hi _ (by simp) f
      refine ⟨g (e.symm 1), ?_⟩
      have h := ConcreteCategory.congr_hom hg (e.symm 1)
      simpa [f, e] using h
    exact (ConcreteCategory.isIso_iff_bijective i).2
      ⟨(ModuleCat.mono_iff_injective i).1 inferInstance, hsurj⟩

private lemma rankOne_le_isFinitelyPresentable :
    ObjectProperty.singleton
        (ModuleCat.of R (Shrink.{max u v} R) : ModuleCat.{max u v} R) ≤
      ObjectProperty.isFinitelyPresentable.{max u v} (ModuleCat.{max u v} R) := by
  intro X hX
  rw [ObjectProperty.singleton_iff] at hX
  subst X
  -- Local instance justification (proof-local temporary data): finite presentation of the
  -- rank-one module supplies categorical finite presentability through the canonical instance.
  letI : Module.FinitePresentation R (Shrink.{max u v} R) :=
    Module.FinitePresentation.of_equiv (Shrink.linearEquiv.{max u v} R R).symm
  change CategoryTheory.IsFinitelyPresentable.{max u v}
    (ModuleCat.of R (Shrink.{max u v} R) : ModuleCat.{max u v} R)
  infer_instance

/-- The module category in the canonical universe is locally finitely presentable. -/
noncomputable instance isLocallyFinitelyPresentable :
    IsLocallyFinitelyPresentable.{max u v} (ModuleCat.{max u v} R) := by
  change IsCardinalLocallyPresentable (ModuleCat.{max u v} R) Cardinal.aleph0
  rw [IsCardinalLocallyPresentable.iff_exists_isStrongGenerator]
  exact ⟨ObjectProperty.singleton
      (ModuleCat.of R (Shrink.{max u v} R) : ModuleCat.{max u v} R),
    inferInstance, rankOneStrongGenerator (R := R),
    rankOne_le_isFinitelyPresentable (R := R)⟩

private lemma isFinitelyPresentable_le_isFinitePresentation :
    ObjectProperty.isFinitelyPresentable.{max u v} (ModuleCat.{max u v} R) ≤
      isFinitePresentation.{u, max u v} R := by
  have hclosure :
      (ObjectProperty.singleton
          (ModuleCat.of R (Shrink.{max u v} R) : ModuleCat.{max u v} R)).colimitsCardinalClosure
            Cardinal.aleph0 ≤ isFinitePresentation.{u, max u v} R := by
    apply ObjectProperty.colimitsCardinalClosure_le
    · intro J _ hJ
      -- Local instance justification (proof-local temporary data): the cardinality bound gives
      -- finiteness of the arrow type for this finite-colimit argument.
      haveI : Finite (Arrow J) := (hasCardinalLT_aleph0_iff _).mp hJ
      -- Local instance justification (noncanonical choice): a `FinCategory` structure is chosen
      -- from the finite arrow type only for this closure proof.
      letI : FinCategory J := Classical.choice ((Arrow.finite_iff J).mp inferInstance)
      exact isFinitePresentation_closedUnderFiniteColimits (R := R) J
    · intro X hX
      rw [ObjectProperty.singleton_iff] at hX
      subst X
      change Module.FinitePresentation R (Shrink.{max u v} R)
      exact Module.FinitePresentation.of_equiv (Shrink.linearEquiv.{max u v} R R).symm
  rw [ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable,
    CategoryTheory.IsStrongGenerator.colimitsCardinalClosure_eq_isCardinalPresentable
      (κ := Cardinal.aleph0.{max u v}) (rankOneStrongGenerator (R := R))
      (rankOne_le_isFinitelyPresentable (R := R))]
  exact hclosure

/-- Categorical finite presentability agrees with ordinary finite presentation for bundled
modules in the canonical universe. -/
@[stacks 00HA "categorical and algebraic finite presentation agree"]
theorem isFinitelyPresentable_iff_finitePresentation (P : ModuleCat.{max u v} R) :
    CategoryTheory.IsFinitelyPresentable.{max u v} P ↔ Module.FinitePresentation R P := by
  constructor
  · exact isFinitelyPresentable_le_isFinitePresentation (R := R) P
  · exact Module.FinitePresentation.isFinitelyPresentable (R := R)

/-- Every module is a filtered colimit of finitely presented modules. -/
@[stacks 00HA]
theorem isFinitePresentation_ind (M : ModuleCat.{max u v} R) :
    (isFinitePresentation.{u, max u v} R).ind.{max u v} M := by
  have hle : isFinitePresentation.{u, max u v} R ≤
      ObjectProperty.isFinitelyPresentable.{max u v} (ModuleCat.{max u v} R) := by
    intro X hX
    -- Local instance justification (proof-local temporary data): membership in the object
    -- property supplies the canonical categorical presentability instance.
    letI : Module.FinitePresentation R X := hX
    change CategoryTheory.IsFinitelyPresentable.{max u v} X
    infer_instance
  rw [ObjectProperty.ind_iff_exists hle]
  intro Z g hZ
  exact ⟨Z, 𝟙 Z, g, by simp,
    (isFinitelyPresentable_iff_finitePresentation (R := R) Z).mp hZ⟩

end

end ModuleCat

namespace Module.FinitePresentation

/-- The regular right module of a ring is finitely presented over its opposite ring. -/
theorem rightRegular (A : Type u) [Ring A] :
    Module.FinitePresentation Aᵐᵒᵖ A := sorry

end Module.FinitePresentation
