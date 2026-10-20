module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.TripleEulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Restriction.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.CategoryTheory.Monoidal.InvertiblePower.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Topology.KrullDimension

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.CoherentTriple

/-- Integral powers of identified invertible modules have canonically identified pullback
and restriction. -/
noncomputable def tensorPowerComparison (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (L : S.U.toScheme.Modules) (L₀ : S.Y.Modules) [Invertible L] [Invertible L₀],
      (eL : (pullback (S.y ∣_ S.U)).obj L ≅ L₀.restrict U₀.ι) →
      ∀ n : ℤ, (pullback (S.y ∣_ S.U)).obj (tensorPowerInt L n) ≅
        (tensorPowerInt L₀ n).restrict U₀.ι := by
  let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
  let U₀ := S.y ⁻¹ᵁ S.U
  exact fun L L₀ _ _ eL n =>
    InvertiblePower.mapIsoOf (pullback (S.y ∣_ S.U)) L
        (SheafOfModules.unit S.U.toScheme.ringCatSheaf)
        ((pullback (S.y ∣_ S.U)).mapIso
            (SheafOfModules.RingedSite.unitIsoTensorUnit
              (J := Opens.grothendieckTopology S.U.toScheme.toTopCat)
              (𝒪 := S.U.toScheme.sheaf)) ≪≫
          (Functor.Monoidal.εIso (pullback (S.y ∣_ S.U))).symm) n ≪≫
      InvertiblePower.factorIso eL n ≪≫
        (InvertiblePower.mapIsoOf (restrictFunctor U₀.ι) L₀
          (SheafOfModules.unit S.Y.ringCatSheaf)
          ((restrictFunctor U₀.ι).mapIso
              (SheafOfModules.RingedSite.unitIsoTensorUnit
                (J := Opens.grothendieckTopology S.Y.toTopCat)
                (𝒪 := S.Y.sheaf)) ≪≫
            (Functor.Monoidal.εIso (restrictFunctor U₀.ι)).symm) n).symm

/-- The integral-power comparison is the composite of monoidal-functor and factor comparisons. -/
theorem tensorPowerComparison_def (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (L : S.U.toScheme.Modules) (L₀ : S.Y.Modules) [Invertible L] [Invertible L₀],
      (eL : (pullback (S.y ∣_ S.U)).obj L ≅ L₀.restrict U₀.ι) →
      ∀ n : ℤ, tensorPowerComparison A f hf_mem L L₀ eL n =
      InvertiblePower.mapIsoOf (pullback (S.y ∣_ S.U)) L
        (SheafOfModules.unit S.U.toScheme.ringCatSheaf)
        ((pullback (S.y ∣_ S.U)).mapIso
            (SheafOfModules.RingedSite.unitIsoTensorUnit
              (J := Opens.grothendieckTopology S.U.toScheme.toTopCat)
              (𝒪 := S.U.toScheme.sheaf)) ≪≫
          (Functor.Monoidal.εIso (pullback (S.y ∣_ S.U))).symm) n ≪≫
      InvertiblePower.factorIso eL n ≪≫
        (InvertiblePower.mapIsoOf (restrictFunctor U₀.ι) L₀
          (SheafOfModules.unit S.Y.ringCatSheaf)
          ((restrictFunctor U₀.ι).mapIso
              (SheafOfModules.RingedSite.unitIsoTensorUnit
                (J := Opens.grothendieckTopology S.Y.toTopCat)
                (𝒪 := S.Y.sheaf)) ≪≫
            (Functor.Monoidal.εIso (restrictFunctor U₀.ι)).symm) n).symm := by
  intros
  rfl

/-- Tensoring a fixed comparison with the canonical integral-power comparison identifies
the twisted components. -/
noncomputable def twistComparison (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (F : S.U.toScheme.Modules) (F₀ : S.Y.Modules)
      (L : S.U.toScheme.Modules) (L₀ : S.Y.Modules) [Invertible L] [Invertible L₀],
      (α : (pullback (S.y ∣_ S.U)).obj F ≅ F₀.restrict U₀.ι) →
      (eL : (pullback (S.y ∣_ S.U)).obj L ≅ L₀.restrict U₀.ι) →
      ∀ n : ℤ, (pullback (S.y ∣_ S.U)).obj (twistByTensorPower L F n) ≅
        (twistByTensorPower L₀ F₀ n).restrict U₀.ι := by
  let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
  let U₀ := S.y ⁻¹ᵁ S.U
  exact fun F F₀ L L₀ _ _ α eL n =>
    pullbackTensorIso (S.y ∣_ S.U) F (tensorPowerInt L n) ≪≫
      (α ⊗ᵢ tensorPowerComparison A f hf_mem L L₀ eL n) ≪≫
        (((restrictFunctorIsoPullback U₀.ι).app (F₀ ⊗ tensorPowerInt L₀ n)) ≪≫
          pullbackTensorIso U₀.ι F₀ (tensorPowerInt L₀ n) ≪≫
          (((restrictFunctorIsoPullback U₀.ι).app F₀).symm ⊗ᵢ
            ((restrictFunctorIsoPullback U₀.ι).app (tensorPowerInt L₀ n)).symm)).symm

/-- The twist comparison is the composite of the pullback-tensor, component, and restriction-tensor comparisons. -/
theorem twistComparison_def (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (F : S.U.toScheme.Modules) (F₀ : S.Y.Modules)
      (L : S.U.toScheme.Modules) (L₀ : S.Y.Modules) [Invertible L] [Invertible L₀],
      (α : (pullback (S.y ∣_ S.U)).obj F ≅ F₀.restrict U₀.ι) →
      (eL : (pullback (S.y ∣_ S.U)).obj L ≅ L₀.restrict U₀.ι) →
      ∀ n : ℤ, twistComparison A f hf_mem F F₀ L L₀ α eL n =
      pullbackTensorIso (S.y ∣_ S.U) F (tensorPowerInt L n) ≪≫
      (α ⊗ᵢ tensorPowerComparison A f hf_mem L L₀ eL n) ≪≫
        (((restrictFunctorIsoPullback U₀.ι).app (F₀ ⊗ tensorPowerInt L₀ n)) ≪≫
          pullbackTensorIso U₀.ι F₀ (tensorPowerInt L₀ n) ≪≫
          (((restrictFunctorIsoPullback U₀.ι).app F₀).symm ⊗ᵢ
            ((restrictFunctorIsoPullback U₀.ι).app (tensorPowerInt L₀ n)).symm)).symm := by
  intros
  rfl

/-- The Euler characteristic of a coherent comparison twisted by an integral power of an
invertible comparison. -/
noncomputable def twistEulerCharacteristic (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (F : S.U.toScheme.Modules) (F₀ : S.Y.Modules)
      (L : S.U.toScheme.Modules) (L₀ : S.Y.Modules)
      [F.IsCoherent] [F₀.IsCoherent] [Invertible L] [Invertible L₀],
      (hF : ∀ V : S.U.toScheme.Opens, Function.Injective
        (F.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
      (α : (pullback (S.y ∣_ S.U)).obj F ≅ F₀.restrict U₀.ι) →
      (eL : (pullback (S.y ∣_ S.U)).obj L ≅ L₀.restrict U₀.ι) →
      ℤ → ℤ := by
  let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
  let U₀ := S.y ⁻¹ᵁ S.U
  exact fun F F₀ L L₀ _ _ _ _ hF α eL n =>
    eulerCharacteristic A f hf_mem
      (F ⊗ tensorPowerInt L n) (F₀ ⊗ tensorPowerInt L₀ n)
      (fun V => smul_injective_tensor F (tensorPowerInt L n) V
        (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f))) (hF V))
      (twistComparison A f hf_mem F F₀ L L₀ α eL n)

/-- The twisted Euler value is the intrinsic Euler characteristic of the componentwise twist. -/
theorem twistEulerCharacteristic_def (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (F : S.U.toScheme.Modules) (F₀ : S.Y.Modules)
      (L : S.U.toScheme.Modules) (L₀ : S.Y.Modules)
      [F.IsCoherent] [F₀.IsCoherent] [Invertible L] [Invertible L₀],
      (hF : ∀ V : S.U.toScheme.Opens, Function.Injective
        (F.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
      (α : (pullback (S.y ∣_ S.U)).obj F ≅ F₀.restrict U₀.ι) →
      (eL : (pullback (S.y ∣_ S.U)).obj L ≅ L₀.restrict U₀.ι) →
      ∀ n : ℤ, twistEulerCharacteristic A f hf_mem F F₀ L L₀ hF α eL n =
      eulerCharacteristic A f hf_mem
      (F ⊗ tensorPowerInt L n) (F₀ ⊗ tensorPowerInt L₀ n)
      (fun V => smul_injective_tensor F (tensorPowerInt L n) V
        (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f))) (hF V))
      (twistComparison A f hf_mem F F₀ L L₀ α eL n) := by
  intros
  rfl

/-- The Euler values of all integral twists of a coherent triple by an invertible triple
agree with a rational polynomial of degree bounded by the punctured support dimension,
with degree zero allowed for empty support. -/
theorem eulerCharacteristic_tensorPower_degreeLE (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (F : S.U.toScheme.Modules) (F₀ : S.Y.Modules)
      (L : S.U.toScheme.Modules) (L₀ : S.Y.Modules)
      [F.IsCoherent] [F₀.IsCoherent] [L.IsCoherent] [L₀.IsCoherent]
      [Invertible L] [Invertible L₀],
      (hF : ∀ V : S.U.toScheme.Opens, Function.Injective
        (F.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
      (hL : ∀ V : S.U.toScheme.Opens, Function.Injective
        (L.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
      (α : (pullback (S.y ∣_ S.U)).obj F ≅ F₀.restrict U₀.ι) →
      (eL : (pullback (S.y ∣_ S.U)).obj L ≅ L₀.restrict U₀.ι) →
      ∃ p : Polynomial ℚ,
        (∀ n : ℤ, p.eval (n : ℚ) =
          (twistEulerCharacteristic A f hf_mem F F₀ L L₀ hF α eL n : ℚ)) ∧
        (p.natDegree : WithBot ℕ∞) ≤
          max 0 (topologicalKrullDim (moduleSupport F)) := sorry

end AlgebraicGeometry.Scheme.Modules.CoherentTriple
