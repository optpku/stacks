/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.«52_25_1_1_EulerCharacteristic»
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Power
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower.Comparison
public import ReasLib.CategoryTheory.Monoidal.Invertible.Duality
import Mathlib.CategoryTheory.Monoidal.Category

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.CoherentTriple

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {S : CoherentTripleSetup A}

/-- A coherent triple is invertible when both of its module components are tensor-invertible. -/
class IsInvertible (L : CoherentTriple S) : Prop where
  /-- Invertibility of the module on the punctured scheme. -/
  invertible_F : Scheme.Modules.Invertible L.F
  /-- Invertibility of the module on the closed fibre. -/
  invertible_F₀ : Scheme.Modules.Invertible L.F₀

/-- The punctured-scheme component of an invertible coherent triple is invertible. -/
instance IsInvertible.instInvertible_F (L : CoherentTriple S) [hL : L.IsInvertible] :
    Scheme.Modules.Invertible L.F := hL.invertible_F

/-- The closed-fibre component of an invertible coherent triple is invertible. -/
instance IsInvertible.instInvertible_F₀ (L : CoherentTriple S) [hL : L.IsInvertible] :
    Scheme.Modules.Invertible L.F₀ := hL.invertible_F₀

/-- Componentwise invertibility assembles into an invertible coherent triple. -/
instance instIsInvertible_of_components (L : CoherentTriple S)
    [Scheme.Modules.Invertible L.F] [Scheme.Modules.Invertible L.F₀] : L.IsInvertible :=
  { invertible_F := inferInstance
    invertible_F₀ := inferInstance }

/-- Invertibility of a coherent triple is equivalent to invertibility of both components. -/
theorem isInvertible_iff (L : CoherentTriple S) :
    L.IsInvertible ↔
      Scheme.Modules.Invertible L.F ∧ Scheme.Modules.Invertible L.F₀ := sorry

/-- The monoidal unit coherent triple on the affine-local setup. -/
noncomputable def tensorUnit : CoherentTriple S :=
  { F := 𝟙_ S.algebraization.U.toScheme.Modules
    F₀ := 𝟙_ S.algebraization.Y.Modules
    coherent_F := by sorry
    coherent_F₀ := by sorry
    mul_f_injective := by sorry
    α :=
      Scheme.Modules.pullbackUnitIso S.closedFiberOnU ≪≫
        (Scheme.Modules.pullbackUnitIso S.algebraization.U₀.ι).symm ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback S.algebraization.U₀.ι).app
          (𝟙_ S.algebraization.Y.Modules)).symm }

/-- The punctured component of `tensorUnit` is the tensor unit. -/
theorem tensorUnit_F : (tensorUnit (S := S)).F = 𝟙_ S.algebraization.U.toScheme.Modules := sorry

/-- The closed-fibre component of `tensorUnit` is the tensor unit. -/
theorem tensorUnit_F₀ : (tensorUnit (S := S)).F₀ = 𝟙_ S.algebraization.Y.Modules := sorry

/-- The coherent tensor unit is invertible componentwise. -/
instance tensorUnit_isInvertible : (tensorUnit (S := S)).IsInvertible := sorry

/-- The tensor product of two coherent triples, with the componentwise comparison isomorphism. -/
noncomputable def tensor (T U : CoherentTriple S) [U.IsInvertible] : CoherentTriple S :=
  { F := T.F ⊗ U.F
    F₀ := T.F₀ ⊗ U.F₀
    coherent_F := by sorry
    coherent_F₀ := by sorry
    mul_f_injective := by sorry
    α :=
      (Scheme.Modules.pullbackTensorIso S.closedFiberOnU T.F U.F) ≪≫
        (T.α ⊗ᵢ U.α) ≪≫
        (((Scheme.Modules.restrictFunctorIsoPullback S.algebraization.U₀.ι).app
          (T.F₀ ⊗ U.F₀)) ≪≫
          Scheme.Modules.pullbackTensorIso S.algebraization.U₀.ι T.F₀ U.F₀ ≪≫
          (((Scheme.Modules.restrictFunctorIsoPullback S.algebraization.U₀.ι).app T.F₀).symm
            ⊗ᵢ ((Scheme.Modules.restrictFunctorIsoPullback S.algebraization.U₀.ι).app U.F₀).symm)).symm }

/-- The punctured component of a coherent-triple tensor product. -/
theorem tensor_F (T U : CoherentTriple S) [U.IsInvertible] :
    (tensor T U).F = T.F ⊗ U.F := sorry

/-- The closed-fibre component of a coherent-triple tensor product. -/
theorem tensor_F₀ (T U : CoherentTriple S) [U.IsInvertible] :
    (tensor T U).F₀ = T.F₀ ⊗ U.F₀ := sorry

/-- The coherent-triple tensor construction has the stated componentwise comparison. -/
theorem tensor_spec (T U : CoherentTriple S) [U.IsInvertible] :
    (tensor T U).α =
      (Scheme.Modules.pullbackTensorIso S.closedFiberOnU T.F U.F) ≪≫
        (T.α ⊗ᵢ U.α) ≪≫
        (((Scheme.Modules.restrictFunctorIsoPullback S.algebraization.U₀.ι).app
          (T.F₀ ⊗ U.F₀)) ≪≫
          Scheme.Modules.pullbackTensorIso S.algebraization.U₀.ι T.F₀ U.F₀ ≪≫
          (((Scheme.Modules.restrictFunctorIsoPullback S.algebraization.U₀.ι).app T.F₀).symm
            ⊗ᵢ ((Scheme.Modules.restrictFunctorIsoPullback S.algebraization.U₀.ι).app U.F₀).symm)).symm := sorry

/-- The scheme-module pullback functor carries the canonical strong-monoidal structure. -/
noncomputable instance pullbackFunctorMonoidal {X Y : Scheme} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f

/-- Restriction along an open immersion inherits a strong-monoidal structure from pullback. -/
noncomputable instance restrictionFunctorMonoidal {X Y : Scheme} (f : X ⟶ Y)
    [IsOpenImmersion f] : (Scheme.Modules.restrictFunctor f).Monoidal :=
  let e := Scheme.Modules.restrictFunctorIsoPullback f
  let p := Scheme.Modules.pullbackUnitIso f
  { ε := p.inv ≫ (e.inv.app _)
    η := (e.hom.app _) ≫ p.hom
    μ := fun X Y ↦
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫
        (Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) X Y) ≫ e.inv.app (X ⊗ Y)
    δ := fun X Y ↦
      e.hom.app (X ⊗ Y) ≫
        (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) X Y) ≫
          (e.inv.app X ⊗ₘ e.inv.app Y)
    μ_natural_left := sorry
    μ_natural_right := sorry
    ε_η := sorry
    η_ε := sorry
    μ_δ := sorry
    δ_μ := sorry
    associativity := sorry
    left_unitality := sorry
    right_unitality := sorry
    δ_natural_left := sorry
    δ_natural_right := sorry
    oplax_associativity := sorry
    oplax_left_unitality := sorry
    oplax_right_unitality := sorry }

section IntegralPowerComparisons

open CategoryTheory
open CategoryTheory.MonoidalCategory

variable {C D : Type u} [Category C] [Category D]
variable [MonoidalCategory C] [MonoidalCategory D]

/-- The degree-minus-one comparison induced by an isomorphism of invertible factors. -/
noncomputable def integralPowerFactorIsoNegOne
    {L L' : C} [isInvertibleObject L] [isInvertibleObject L'] (e : L ≅ L') :
    CategoryTheory.MonoidalCategory.InvertiblePower.obj L (-1 : ℤ) ≅
      CategoryTheory.MonoidalCategory.InvertiblePower.obj L' (-1 : ℤ) :=
  let pL := ExactPairing.ofTensorInverse
    (InvertiblePower.evaluationIso L) (InvertiblePower.rightEvaluationIso L)
  let pL' := ExactPairing.ofTensorInverse
    (InvertiblePower.evaluationIso L') (InvertiblePower.rightEvaluationIso L')
  let transported : ExactPairing L'
      (CategoryTheory.MonoidalCategory.InvertiblePower.obj L (-1 : ℤ)) :=
    { coevaluation' :=
        pL.coevaluation' ≫
          (e ⊗ᵢ Iso.refl
            (CategoryTheory.MonoidalCategory.InvertiblePower.obj L (-1 : ℤ))).hom
      evaluation' :=
        (Iso.refl
            (CategoryTheory.MonoidalCategory.InvertiblePower.obj L (-1 : ℤ)) ⊗ᵢ e.symm).hom ≫
          pL.evaluation'
      coevaluation_evaluation' := sorry
      evaluation_coevaluation' := sorry }
  MonoidalCategory.isInvertibleObject.inverseIso L' transported ≪≫
    (MonoidalCategory.isInvertibleObject.inverseIso L' pL').symm

/-- The nonnegative integral-power comparison induced by an isomorphism of factors. -/
noncomputable def integralPowerFactorIsoNat
    {L L' : C} [isInvertibleObject L] [isInvertibleObject L'] (e : L ≅ L') :
    (n : ℕ) →
      CategoryTheory.MonoidalCategory.InvertiblePower.obj L (n : ℤ) ≅
        CategoryTheory.MonoidalCategory.InvertiblePower.obj L' (n : ℤ)
  | 0 =>
      CategoryTheory.MonoidalCategory.InvertiblePower.zeroIso L ≪≫
        (CategoryTheory.MonoidalCategory.InvertiblePower.zeroIso L').symm
  | n + 1 =>
      (CategoryTheory.MonoidalCategory.InvertiblePower.rightSuccIso L (n : ℤ)).symm ≪≫
        (integralPowerFactorIsoNat e n ⊗ᵢ e) ≪≫
          CategoryTheory.MonoidalCategory.InvertiblePower.rightSuccIso L' (n : ℤ)

/-- The negative integral-power comparison induced by an isomorphism of factors. -/
noncomputable def integralPowerFactorIsoNeg
    {L L' : C} [isInvertibleObject L] [isInvertibleObject L'] (e : L ≅ L') :
    (n : ℕ) →
      CategoryTheory.MonoidalCategory.InvertiblePower.obj L (Int.negSucc n) ≅
        CategoryTheory.MonoidalCategory.InvertiblePower.obj L' (Int.negSucc n)
  | 0 => integralPowerFactorIsoNegOne e
  | n + 1 =>
      CategoryTheory.MonoidalCategory.InvertiblePower.negSuccIso L n ≪≫
        (integralPowerFactorIsoNegOne e ⊗ᵢ integralPowerFactorIsoNeg e n) ≪≫
          (CategoryTheory.MonoidalCategory.InvertiblePower.negSuccIso L' n).symm

/-- The canonical map between integral powers induced by an isomorphism of invertible factors. -/
noncomputable def integralPowerFactorIso
    {L L' : C} [isInvertibleObject L] [isInvertibleObject L'] (e : L ≅ L') (n : ℤ) :
    CategoryTheory.MonoidalCategory.InvertiblePower.obj L n ≅
      CategoryTheory.MonoidalCategory.InvertiblePower.obj L' n :=
  match n with
  | .ofNat n => integralPowerFactorIsoNat e n
  | .negSucc n => integralPowerFactorIsoNeg e n

/-- The zero-degree factor comparison is compatible with the canonical unit comparisons. -/
theorem integralPowerFactorIso_zero
    {L L' : C} [isInvertibleObject L] [isInvertibleObject L'] (e : L ≅ L') :
    integralPowerFactorIso e 0 =
      CategoryTheory.MonoidalCategory.InvertiblePower.zeroIso L ≪≫
        (CategoryTheory.MonoidalCategory.InvertiblePower.zeroIso L').symm := sorry

/-- The degree-one factor comparison is induced by the original factor isomorphism. -/
theorem integralPowerFactorIso_one
    {L L' : C} [isInvertibleObject L] [isInvertibleObject L'] (e : L ≅ L') :
    integralPowerFactorIso e 1 ≪≫
        CategoryTheory.MonoidalCategory.InvertiblePower.oneIso L' =
      CategoryTheory.MonoidalCategory.InvertiblePower.oneIso L ≪≫ e := sorry

/-- Factor comparisons commute with addition of integral exponents. -/
theorem integralPowerFactorIso_add
    {L L' : C} [isInvertibleObject L] [isInvertibleObject L'] (e : L ≅ L') (m n : ℤ) :
    CategoryTheory.MonoidalCategory.InvertiblePower.addIso L m n ≪≫
          integralPowerFactorIso e (m + n) =
      (integralPowerFactorIso e m ⊗ᵢ integralPowerFactorIso e n) ≪≫
        CategoryTheory.MonoidalCategory.InvertiblePower.addIso L' m n := sorry

/-- The degree-minus-one comparison for the image of an integral power under a monoidal functor. -/
noncomputable def integralPowerObjectMapIsoNegOne
    (F : C ⥤ D) [F.Monoidal] (L : C) [isInvertibleObject L] :
    F.obj (CategoryTheory.MonoidalCategory.InvertiblePower.obj L (-1 : ℤ)) ≅
      CategoryTheory.MonoidalCategory.InvertiblePower.obj (F.obj L) (-1 : ℤ) :=
  let pL := ExactPairing.ofTensorInverse
    (InvertiblePower.evaluationIso L) (InvertiblePower.rightEvaluationIso L)
  let pF := ExactPairing.ofTensorInverse
    (InvertiblePower.evaluationIso (F.obj L))
    (InvertiblePower.rightEvaluationIso (F.obj L))
  MonoidalCategory.isInvertibleObject.inverseIso (F.obj L) (pL.map F) ≪≫
    (MonoidalCategory.isInvertibleObject.inverseIso (F.obj L) pF).symm

/-- The nonnegative comparison between an image of an integral power and the power of the image. -/
noncomputable def integralPowerObjectMapIsoNat
    (F : C ⥤ D) [F.Monoidal] (L : C) [isInvertibleObject L] :
    (n : ℕ) →
      F.obj (CategoryTheory.MonoidalCategory.InvertiblePower.obj L (n : ℤ)) ≅
        CategoryTheory.MonoidalCategory.InvertiblePower.obj (F.obj L) (n : ℤ)
  | 0 =>
      F.mapIso (CategoryTheory.MonoidalCategory.InvertiblePower.zeroIso L) ≪≫
        (Functor.Monoidal.εIso F).symm ≪≫
          (CategoryTheory.MonoidalCategory.InvertiblePower.zeroIso (F.obj L)).symm
  | n + 1 =>
      (F.mapIso
          (CategoryTheory.MonoidalCategory.InvertiblePower.rightSuccIso L (n : ℤ))).symm ≪≫
        (Functor.Monoidal.μIso F
          (CategoryTheory.MonoidalCategory.InvertiblePower.obj L (n : ℤ)) L).symm ≪≫
          (integralPowerObjectMapIsoNat F L n ⊗ᵢ Iso.refl (F.obj L)) ≪≫
            CategoryTheory.MonoidalCategory.InvertiblePower.rightSuccIso (F.obj L) (n : ℤ)

/-- The negative comparison between an image of an integral power and the power of the image. -/
noncomputable def integralPowerObjectMapIsoNeg
    (F : C ⥤ D) [F.Monoidal] (L : C) [isInvertibleObject L] :
    (n : ℕ) →
      F.obj (CategoryTheory.MonoidalCategory.InvertiblePower.obj L (Int.negSucc n)) ≅
        CategoryTheory.MonoidalCategory.InvertiblePower.obj (F.obj L) (Int.negSucc n)
  | 0 => integralPowerObjectMapIsoNegOne F L
  | n + 1 =>
      F.mapIso (CategoryTheory.MonoidalCategory.InvertiblePower.negSuccIso L n) ≪≫
        (Functor.Monoidal.μIso F
          (CategoryTheory.MonoidalCategory.InvertiblePower.obj L (-1 : ℤ))
          (CategoryTheory.MonoidalCategory.InvertiblePower.obj L (Int.negSucc n))).symm ≪≫
          (integralPowerObjectMapIsoNegOne F L ⊗ᵢ
            integralPowerObjectMapIsoNeg F L n) ≪≫
            (CategoryTheory.MonoidalCategory.InvertiblePower.negSuccIso (F.obj L) n).symm

/-- The canonical comparison between the image of an integral power and the integral power of an
image, built from the monoidal unit/tensor comparisons. -/
noncomputable def integralPowerObjectMapIso
    (F : C ⥤ D) [F.Monoidal] (L : C) [isInvertibleObject L] (n : ℤ) :
    F.obj (CategoryTheory.MonoidalCategory.InvertiblePower.obj L n) ≅
      CategoryTheory.MonoidalCategory.InvertiblePower.obj (F.obj L) n :=
  match n with
  | .ofNat n => integralPowerObjectMapIsoNat F L n
  | .negSucc n => integralPowerObjectMapIsoNeg F L n

/-- The monoidal-functor comparison for integral powers evaluated at an arbitrary base object. -/
noncomputable def integralPowerMapIso
    (F : C ⥤ D) [F.Monoidal] (L A : C) [isInvertibleObject L] (n : ℤ) :
    F.obj (CategoryTheory.MonoidalCategory.InvertiblePower.eval L A n) ≅
      CategoryTheory.MonoidalCategory.InvertiblePower.eval (F.obj L) (F.obj A) n :=
  F.mapIso (CategoryTheory.MonoidalCategory.InvertiblePower.evalTensorIso L A n) ≪≫
    (Functor.Monoidal.μIso F A
      (CategoryTheory.MonoidalCategory.InvertiblePower.obj L n)).symm ≪≫
      (Iso.refl (F.obj A) ⊗ᵢ integralPowerObjectMapIso F L n) ≪≫
        (CategoryTheory.MonoidalCategory.InvertiblePower.evalTensorIso
          (F.obj L) (F.obj A) n).symm

/-- Transport the base object of an integral-power comparison along a specified isomorphism. -/
noncomputable def integralPowerMapIsoOf
    (F : C ⥤ D) [F.Monoidal] (L U : C) [isInvertibleObject L]
    {V : D} (u : F.obj U ≅ V) (n : ℤ) :
    F.obj (CategoryTheory.MonoidalCategory.InvertiblePower.eval L U n) ≅
      CategoryTheory.MonoidalCategory.InvertiblePower.eval (F.obj L) V n :=
  integralPowerMapIso F L U n ≪≫
    CategoryTheory.MonoidalCategory.InvertiblePower.evalMapIso (F.obj L) u n

end IntegralPowerComparisons

/-- An explicit comparison identifies the pullback of an integral tensor power with the
restriction of the corresponding closed-fibre power. -/
abbrev TensorPowerComparison (L : CoherentTriple S) [L.IsInvertible] (n : ℤ) :=
  (Scheme.Modules.pullback S.closedFiberOnU).obj
      (Scheme.Modules.tensorPowerInt L.F n) ≅
    (Scheme.Modules.tensorPowerInt L.F₀ n).restrict S.algebraization.U₀.ι

/-- The coherent triple formed by the componentwise integral powers of an invertible triple. -/
noncomputable def tensorPower (L : CoherentTriple S) [L.IsInvertible] (n : ℤ)
    (α : TensorPowerComparison L n) : CoherentTriple S :=
  { F := Scheme.Modules.tensorPowerInt L.F n
    F₀ := Scheme.Modules.tensorPowerInt L.F₀ n
    coherent_F := by sorry
    coherent_F₀ := by sorry
    mul_f_injective := by sorry
    α := α }

/-- The punctured component of an integral coherent-triple power. -/
theorem tensorPower_F (L : CoherentTriple S) [L.IsInvertible] (n : ℤ)
    (α : TensorPowerComparison L n) :
    (tensorPower L n α).F = Scheme.Modules.tensorPowerInt L.F n := sorry

/-- The closed-fibre component of an integral coherent-triple power. -/
theorem tensorPower_F₀ (L : CoherentTriple S) [L.IsInvertible] (n : ℤ)
    (α : TensorPowerComparison L n) :
    (tensorPower L n α).F₀ = Scheme.Modules.tensorPowerInt L.F₀ n := sorry

/-- The comparison stored by an integral coherent-triple power is an isomorphism. -/
theorem tensorPower_alpha_isIso (L : CoherentTriple S) [L.IsInvertible] (n : ℤ)
    (α : TensorPowerComparison L n) : IsIso (tensorPower L n α).α.hom := sorry

/-- A comparison is available for every canonical integral tensor power. -/
theorem existsTensorPowerComparison (L : CoherentTriple S) [L.IsInvertible] (n : ℤ) :
    Nonempty (TensorPowerComparison L n) := sorry

/-- The canonical chosen comparison for an integral tensor power. -/
noncomputable def canonicalTensorPowerComparison
    (L : CoherentTriple S) [L.IsInvertible] (n : ℤ) : TensorPowerComparison L n :=
  integralPowerMapIsoOf (Scheme.Modules.pullback S.closedFiberOnU) L.F
      (SheafOfModules.unit S.algebraization.U.toScheme.ringCatSheaf)
      ((Scheme.Modules.pullback S.closedFiberOnU).mapIso
          (SheafOfModules.RingedSite.unitIsoTensorUnit
            (J := Opens.grothendieckTopology S.algebraization.U.toScheme.toTopCat)
            (𝒪 := S.algebraization.U.toScheme.sheaf)) ≪≫
        (Functor.Monoidal.εIso (Scheme.Modules.pullback S.closedFiberOnU)).symm) n ≪≫
    integralPowerFactorIso L.α n ≪≫
      (integralPowerMapIsoOf (Scheme.Modules.restrictFunctor S.algebraization.U₀.ι) L.F₀
        (SheafOfModules.unit S.algebraization.Y.ringCatSheaf)
        ((Scheme.Modules.restrictFunctor S.algebraization.U₀.ι).mapIso
            (SheafOfModules.RingedSite.unitIsoTensorUnit
              (J := Opens.grothendieckTopology S.algebraization.Y.toTopCat)
              (𝒪 := S.algebraization.Y.sheaf)) ≪≫
          (Functor.Monoidal.εIso
            (Scheme.Modules.restrictFunctor S.algebraization.U₀.ι)).symm) n).symm

/-- The canonical tensor-power comparison has the expected hom-inverse identity. -/
theorem canonicalTensorPowerComparison_hom_inv_id
    (L : CoherentTriple S) [L.IsInvertible] (n : ℤ) :
    (canonicalTensorPowerComparison L n).hom ≫
        (canonicalTensorPowerComparison L n).inv = 𝟙 _ := sorry

/-- The coherent triple formed by the canonical integral tensor power of an invertible triple. -/
noncomputable def canonicalTensorPower
    (L : CoherentTriple S) [L.IsInvertible] (n : ℤ) : CoherentTriple S :=
  tensorPower L n (canonicalTensorPowerComparison L n)

/-- The punctured component of the canonical integral coherent-triple power. -/
theorem canonicalTensorPower_F (L : CoherentTriple S) [L.IsInvertible] (n : ℤ) :
    (canonicalTensorPower L n).F = Scheme.Modules.tensorPowerInt L.F n := sorry

/-- The closed-fibre component of the canonical integral coherent-triple power. -/
theorem canonicalTensorPower_F₀ (L : CoherentTriple S) [L.IsInvertible] (n : ℤ) :
    (canonicalTensorPower L n).F₀ = Scheme.Modules.tensorPowerInt L.F₀ n := sorry

/-- Every explicitly compared integral power is an invertible coherent triple. -/
instance instTensorPowerIsInvertible (L : CoherentTriple S) [L.IsInvertible] (n : ℤ)
    (α : TensorPowerComparison L n) : (tensorPower L n α).IsInvertible := sorry

/-- The canonical integral coherent-triple power is invertible. -/
instance instCanonicalTensorPowerIsInvertible
    (L : CoherentTriple S) [L.IsInvertible] (n : ℤ) :
    (canonicalTensorPower L n).IsInvertible :=
  instTensorPowerIsInvertible L n (canonicalTensorPowerComparison L n)

/-- Tensoring a coherent triple by an explicitly compared integral power. -/
noncomputable def twist (F L : CoherentTriple S) [L.IsInvertible] (n : ℤ)
    (α : TensorPowerComparison L n) : CoherentTriple S :=
  tensor F (tensorPower L n α)

/-- The tensor-power presentation of `twist` is definitionally represented by `tensor`. -/
theorem twist_def (F L : CoherentTriple S) [L.IsInvertible] (n : ℤ)
    (α : TensorPowerComparison L n) :
    twist F L n α = tensor F (tensorPower L n α) := sorry

/-- The canonical coherent-triple twist by an integral tensor power. -/
noncomputable def canonicalTwist (F L : CoherentTriple S) [L.IsInvertible] (n : ℤ) :
    CoherentTriple S :=
  tensor F (canonicalTensorPower L n)

/-- The canonical twist is the explicit tensor-power twist for its chosen comparison. -/
theorem canonicalTwist_def (F L : CoherentTriple S) [L.IsInvertible] (n : ℤ) :
    canonicalTwist F L n =
      twist F L n (canonicalTensorPowerComparison L n) := sorry

end AlgebraicGeometry.CoherentTriple
