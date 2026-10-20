module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Ring
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor.Instances
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Bifunctor

/-!
# The second Adams operation on perfect-complex K₀

This file describes the second Adams operation through the positive and negative eigensummands
of canonical factor exchange on derived tensor squares.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0

/-- Two perfect complexes are respectively the positive and negative eigensummands of canonical
factor exchange on the derived tensor square of a perfect complex. -/
noncomputable def IsTensorSquareEigensplitting (X : Scheme.{u})
    (L positive negative : @RingedSpace.ModuleDerived.Perfect X.toRingedSpace) : Prop :=
  -- Local instance justification (defeq pin): the graded tensor existence theorem is stated for the underlying ringed-site presentation of `X.Modules`.
  letI : ∀ G₁ G₂ : GradedObject ℤ (RingedSpace.Modules X.toRingedSpace),
      GradedObject.HasTensor G₁ G₂ :=
    fun G₁ G₂ ↦ SheafOfModules.RingedSite.IntGraded.hasTensor G₁ G₂
  -- Local instance justification (defeq pin): the three-factor coherence theorem uses the same ringed-site presentation as the canonical bifunctorial model.
  letI : ∀ G₁ G₂ G₃ : GradedObject ℤ (RingedSpace.Modules X.toRingedSpace),
      GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃ :=
    fun G₁ G₂ G₃ ↦
      SheafOfModules.RingedSite.IntGraded.hasGoodTensor₁₂Tensor G₁ G₂ G₃
  -- Local instance justification (defeq pin): the other three-factor coherence theorem uses the same ringed-site presentation as the canonical bifunctorial model.
  letI : ∀ G₁ G₂ G₃ : GradedObject ℤ (RingedSpace.Modules X.toRingedSpace),
      GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃ :=
    fun G₁ G₂ G₃ ↦
      SheafOfModules.RingedSite.IntGraded.hasGoodTensorTensor₂₃ G₁ G₂ G₃
  -- Local instance justification (defeq pin): four-factor coherence is specialized to the same ringed-site module category used by `tensorObj`.
  letI : ∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (RingedSpace.Modules X.toRingedSpace),
      GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄ :=
    fun G₁ G₂ G₃ G₄ ↦
      SheafOfModules.RingedSite.IntGraded.hasTensor₄ObjExt G₁ G₂ G₃ G₄
  -- Local instance justification (noncanonical choice): the project deliberately exposes the canonical two-variable derived model as a theorem rather than a global instance.
  letI := Scheme.ModuleDerived.ProjectionFormula.hasDerivedTensorBifunctor X
  let swap : tensorObj X L L ⟶ tensorObj X L L :=
    ⟨(DerivedCategory.DerivedTensor.Bifunctor.Right.comm L.obj L.obj).hom⟩
  ∃ (positiveι : positive ⟶ tensorObj X L L)
      (positiveπ : tensorObj X L L ⟶ positive)
      (negativeι : negative ⟶ tensorObj X L L)
      (negativeπ : tensorObj X L L ⟶ negative),
    positiveι ≫ positiveπ = 𝟙 _ ∧
      negativeι ≫ negativeπ = 𝟙 _ ∧
      positiveπ ≫ positiveι + negativeπ ≫ negativeι = 𝟙 _ ∧
      positiveι ≫ swap = positiveι ∧
      negativeι ≫ swap = -negativeι

/-- An additive endomorphism of perfect-complex `K₀` is the second Adams operation when its
value on every perfect complex is the difference of the positive and negative tensor-square
eigensummand classes. -/
def IsAdamsTwo (X : Scheme.{u}) (psi : K0 X →+ K0 X) : Prop :=
  ∀ L : @RingedSpace.ModuleDerived.Perfect X.toRingedSpace,
    ∃ positive negative : @RingedSpace.ModuleDerived.Perfect X.toRingedSpace,
      IsTensorSquareEigensplitting X L positive negative ∧
        psi (TriangulatedK0.of L) =
          TriangulatedK0.of positive - TriangulatedK0.of negative

/-- If two is invertible on a scheme, its perfect-complex `K₀` admits a second Adams
operation described by tensor-square eigensummands. -/
theorem exists_adamsTwo (X : Scheme.{u}) [Invertible (2 : Γ(X, ⊤))] :
    ∃ psi : K0 X →+ K0 X, IsAdamsTwo X psi := sorry

end AlgebraicGeometry.Scheme.K0
