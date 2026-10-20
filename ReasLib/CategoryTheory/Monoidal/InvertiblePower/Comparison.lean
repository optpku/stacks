module

public import ReasLib.CategoryTheory.Monoidal.InvertiblePower
public import ReasLib.CategoryTheory.Monoidal.Invertible.Duality

@[expose] public section

noncomputable section

universe u

namespace CategoryTheory.MonoidalCategory.InvertiblePower


open CategoryTheory
open CategoryTheory.MonoidalCategory

variable {C D : Type u} [Category C] [Category D]
variable [MonoidalCategory C] [MonoidalCategory D]

/-- Transporting the first factor of an exact pairing preserves its first triangle identity. -/
theorem factorPairing_coevaluation_evaluation
    {L L' M : C} (p : ExactPairing L M) (e : L ≅ L') :
    M ◁ (p.coevaluation' ≫ (e ⊗ᵢ Iso.refl M).hom) ≫
        (α_ M L' M).inv ≫
          ((Iso.refl M ⊗ᵢ e.symm).hom ≫ p.evaluation') ▷ M =
      (ρ_ M).hom ≫ (λ_ M).inv := sorry

/-- Transporting the first factor of an exact pairing preserves its second triangle identity. -/
theorem factorPairing_evaluation_coevaluation
    {L L' M : C} (p : ExactPairing L M) (e : L ≅ L') :
    (p.coevaluation' ≫ (e ⊗ᵢ Iso.refl M).hom) ▷ L' ≫
        (α_ L' M L').hom ≫
          L' ◁ ((Iso.refl M ⊗ᵢ e.symm).hom ≫ p.evaluation') =
      (λ_ L').hom ≫ (ρ_ L').inv := sorry

/-- The degree-minus-one comparison induced by an isomorphism of invertible factors. -/
noncomputable def factorIsoNegOne
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
      coevaluation_evaluation' := factorPairing_coevaluation_evaluation pL e
      evaluation_coevaluation' := factorPairing_evaluation_coevaluation pL e }
  MonoidalCategory.isInvertibleObject.inverseIso L' transported ≪≫
    (MonoidalCategory.isInvertibleObject.inverseIso L' pL').symm

/-- The nonnegative integral-power comparison induced by an isomorphism of factors. -/
noncomputable def factorIsoNat
    {L L' : C} [isInvertibleObject L] [isInvertibleObject L'] (e : L ≅ L') :
    (n : ℕ) →
      CategoryTheory.MonoidalCategory.InvertiblePower.obj L (n : ℤ) ≅
        CategoryTheory.MonoidalCategory.InvertiblePower.obj L' (n : ℤ)
  | 0 =>
      CategoryTheory.MonoidalCategory.InvertiblePower.zeroIso L ≪≫
        (CategoryTheory.MonoidalCategory.InvertiblePower.zeroIso L').symm
  | n + 1 =>
      (CategoryTheory.MonoidalCategory.InvertiblePower.rightSuccIso L (n : ℤ)).symm ≪≫
        (factorIsoNat e n ⊗ᵢ e) ≪≫
          CategoryTheory.MonoidalCategory.InvertiblePower.rightSuccIso L' (n : ℤ)

/-- The negative integral-power comparison induced by an isomorphism of factors. -/
noncomputable def factorIsoNeg
    {L L' : C} [isInvertibleObject L] [isInvertibleObject L'] (e : L ≅ L') :
    (n : ℕ) →
      CategoryTheory.MonoidalCategory.InvertiblePower.obj L (Int.negSucc n) ≅
        CategoryTheory.MonoidalCategory.InvertiblePower.obj L' (Int.negSucc n)
  | 0 => factorIsoNegOne e
  | n + 1 =>
      CategoryTheory.MonoidalCategory.InvertiblePower.negSuccIso L n ≪≫
        (factorIsoNegOne e ⊗ᵢ factorIsoNeg e n) ≪≫
          (CategoryTheory.MonoidalCategory.InvertiblePower.negSuccIso L' n).symm

/-- The canonical map between integral powers induced by an isomorphism of invertible factors. -/
noncomputable def factorIso
    {L L' : C} [isInvertibleObject L] [isInvertibleObject L'] (e : L ≅ L') (n : ℤ) :
    CategoryTheory.MonoidalCategory.InvertiblePower.obj L n ≅
      CategoryTheory.MonoidalCategory.InvertiblePower.obj L' n :=
  match n with
  | .ofNat n => factorIsoNat e n
  | .negSucc n => factorIsoNeg e n

/-- The zero-degree factor comparison is compatible with the canonical unit comparisons. -/
theorem factorIso_zero
    {L L' : C} [isInvertibleObject L] [isInvertibleObject L'] (e : L ≅ L') :
    factorIso e 0 =
      CategoryTheory.MonoidalCategory.InvertiblePower.zeroIso L ≪≫
        (CategoryTheory.MonoidalCategory.InvertiblePower.zeroIso L').symm := sorry

/-- The degree-one factor comparison is induced by the original factor isomorphism. -/
theorem factorIso_one
    {L L' : C} [isInvertibleObject L] [isInvertibleObject L'] (e : L ≅ L') :
    factorIso e 1 ≪≫
        CategoryTheory.MonoidalCategory.InvertiblePower.oneIso L' =
      CategoryTheory.MonoidalCategory.InvertiblePower.oneIso L ≪≫ e := sorry

/-- Factor comparisons commute with addition of integral exponents. -/
theorem factorIso_add
    {L L' : C} [isInvertibleObject L] [isInvertibleObject L'] (e : L ≅ L') (m n : ℤ) :
    CategoryTheory.MonoidalCategory.InvertiblePower.addIso L m n ≪≫
          factorIso e (m + n) =
      (factorIso e m ⊗ᵢ factorIso e n) ≪≫
        CategoryTheory.MonoidalCategory.InvertiblePower.addIso L' m n := sorry

/-- The degree-minus-one comparison for the image of an integral power under a monoidal functor. -/
noncomputable def objectMapIsoNegOne
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
noncomputable def objectMapIsoNat
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
          (objectMapIsoNat F L n ⊗ᵢ Iso.refl (F.obj L)) ≪≫
            CategoryTheory.MonoidalCategory.InvertiblePower.rightSuccIso (F.obj L) (n : ℤ)

/-- The negative comparison between an image of an integral power and the power of the image. -/
noncomputable def objectMapIsoNeg
    (F : C ⥤ D) [F.Monoidal] (L : C) [isInvertibleObject L] :
    (n : ℕ) →
      F.obj (CategoryTheory.MonoidalCategory.InvertiblePower.obj L (Int.negSucc n)) ≅
        CategoryTheory.MonoidalCategory.InvertiblePower.obj (F.obj L) (Int.negSucc n)
  | 0 => objectMapIsoNegOne F L
  | n + 1 =>
      F.mapIso (CategoryTheory.MonoidalCategory.InvertiblePower.negSuccIso L n) ≪≫
        (Functor.Monoidal.μIso F
          (CategoryTheory.MonoidalCategory.InvertiblePower.obj L (-1 : ℤ))
          (CategoryTheory.MonoidalCategory.InvertiblePower.obj L (Int.negSucc n))).symm ≪≫
          (objectMapIsoNegOne F L ⊗ᵢ
            objectMapIsoNeg F L n) ≪≫
            (CategoryTheory.MonoidalCategory.InvertiblePower.negSuccIso (F.obj L) n).symm

/-- The canonical comparison between the image of an integral power and the integral power of an
image, built from the monoidal unit/tensor comparisons. -/
noncomputable def objectMapIso
    (F : C ⥤ D) [F.Monoidal] (L : C) [isInvertibleObject L] (n : ℤ) :
    F.obj (CategoryTheory.MonoidalCategory.InvertiblePower.obj L n) ≅
      CategoryTheory.MonoidalCategory.InvertiblePower.obj (F.obj L) n :=
  match n with
  | .ofNat n => objectMapIsoNat F L n
  | .negSucc n => objectMapIsoNeg F L n

/-- The monoidal-functor comparison for integral powers evaluated at an arbitrary base object. -/
noncomputable def mapIso
    (F : C ⥤ D) [F.Monoidal] (L A : C) [isInvertibleObject L] (n : ℤ) :
    F.obj (CategoryTheory.MonoidalCategory.InvertiblePower.eval L A n) ≅
      CategoryTheory.MonoidalCategory.InvertiblePower.eval (F.obj L) (F.obj A) n :=
  F.mapIso (CategoryTheory.MonoidalCategory.InvertiblePower.evalTensorIso L A n) ≪≫
    (Functor.Monoidal.μIso F A
      (CategoryTheory.MonoidalCategory.InvertiblePower.obj L n)).symm ≪≫
      (Iso.refl (F.obj A) ⊗ᵢ objectMapIso F L n) ≪≫
        (CategoryTheory.MonoidalCategory.InvertiblePower.evalTensorIso
          (F.obj L) (F.obj A) n).symm

/-- Transport the base object of an integral-power comparison along a specified isomorphism. -/
noncomputable def mapIsoOf
    (F : C ⥤ D) [F.Monoidal] (L U : C) [isInvertibleObject L]
    {V : D} (u : F.obj U ≅ V) (n : ℤ) :
    F.obj (CategoryTheory.MonoidalCategory.InvertiblePower.eval L U n) ≅
      CategoryTheory.MonoidalCategory.InvertiblePower.eval (F.obj L) V n :=
  mapIso F L U n ≪≫
    CategoryTheory.MonoidalCategory.InvertiblePower.evalMapIso (F.obj L) u n


end CategoryTheory.MonoidalCategory.InvertiblePower
