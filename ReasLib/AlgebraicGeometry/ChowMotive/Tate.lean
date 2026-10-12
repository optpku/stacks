/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.AlgebraicGeometry.ChowMotive.Duality
public import ReasLib.AlgebraicGeometry.Correspondence.Graph
public import ReasLib.CategoryTheory.Idempotents.Karoubi.Monoidal

@[expose] public section

open CategoryTheory CategoryTheory.Idempotents
open AlgebraicGeometry AlgebraicGeometry.Correspondence
open scoped CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace ChowMotive.Tate

/-- The rational graph of the point-product unitor is compatible with the identity
projectors on point Tate twists. -/
theorem tensorHom_comm (k : Type u) [Field k] (m n : ℤ) :
    let f : (ChowMotive.tateTwist (SchemeOverField.point k) m ⊗
        ChowMotive.tateTwist (SchemeOverField.point k) n).X ⟶
        (ChowMotive.tateTwist (SchemeOverField.point k) (m + n)).X :=
      Correspondence.GradedCategory.homOfDegreeZero rfl
        (Correspondence.rationalGraphIso
          (ChowMotive.tateTwist (SchemeOverField.point k) m ⊗
            ChowMotive.tateTwist (SchemeOverField.point k) n).X.1
          (ChowMotive.tateTwist (SchemeOverField.point k) (m + n)).X.1
          (Correspondence.GradedCategory.leftUnitorSchemeIso
            (Correspondence.GradedCategory.ofScheme (SchemeOverField.point k) n)))
    (ChowMotive.tateTwist (SchemeOverField.point k) m ⊗
        ChowMotive.tateTwist (SchemeOverField.point k) n).p ≫ f ≫
      (ChowMotive.tateTwist (SchemeOverField.point k) (m + n)).p = f := sorry

/-- The point-product unitor as a morphism from the tensor product of two point Tate
twists to the twist whose index is their sum. -/
noncomputable def tensorHom (k : Type u) [Field k] (m n : ℤ) :
    ChowMotive.tateTwist (SchemeOverField.point k) m ⊗
        ChowMotive.tateTwist (SchemeOverField.point k) n ⟶
      ChowMotive.tateTwist (SchemeOverField.point k) (m + n) where
  f := Correspondence.GradedCategory.homOfDegreeZero rfl
    (Correspondence.rationalGraphIso
      (ChowMotive.tateTwist (SchemeOverField.point k) m ⊗
        ChowMotive.tateTwist (SchemeOverField.point k) n).X.1
      (ChowMotive.tateTwist (SchemeOverField.point k) (m + n)).X.1
      (Correspondence.GradedCategory.leftUnitorSchemeIso
        (Correspondence.GradedCategory.ofScheme (SchemeOverField.point k) n)))
  comm := tensorHom_comm k m n

/-- The underlying graded correspondence of `tensorHom` is the rational graph of the
point-product unitor. -/
theorem tensorHom_f (k : Type u) [Field k] (m n : ℤ) :
    (tensorHom k m n).f =
      (Correspondence.GradedCategory.homOfDegreeZero rfl
        (Correspondence.rationalGraphIso
          (ChowMotive.tateTwist (SchemeOverField.point k) m ⊗
            ChowMotive.tateTwist (SchemeOverField.point k) n).X.1
          (ChowMotive.tateTwist (SchemeOverField.point k) (m + n)).X.1
          (Correspondence.GradedCategory.leftUnitorSchemeIso
            (Correspondence.GradedCategory.ofScheme (SchemeOverField.point k) n))) :
        (ChowMotive.tateTwist (SchemeOverField.point k) m ⊗
            ChowMotive.tateTwist (SchemeOverField.point k) n).X ⟶
          (ChowMotive.tateTwist (SchemeOverField.point k) (m + n)).X) := sorry

/-- The inverse point-product unitor is compatible with the identity projectors on point
Tate twists. -/
theorem tensorInv_comm (k : Type u) [Field k] (m n : ℤ) :
    let f : (ChowMotive.tateTwist (SchemeOverField.point k) (m + n)).X ⟶
        (ChowMotive.tateTwist (SchemeOverField.point k) m ⊗
          ChowMotive.tateTwist (SchemeOverField.point k) n).X :=
      Correspondence.GradedCategory.homOfDegreeZero rfl
        (Correspondence.rationalGraphIso
          (ChowMotive.tateTwist (SchemeOverField.point k) (m + n)).X.1
          (ChowMotive.tateTwist (SchemeOverField.point k) m ⊗
            ChowMotive.tateTwist (SchemeOverField.point k) n).X.1
          (Correspondence.GradedCategory.leftUnitorSchemeIso
            (Correspondence.GradedCategory.ofScheme (SchemeOverField.point k) n)).symm)
    (ChowMotive.tateTwist (SchemeOverField.point k) (m + n)).p ≫ f ≫
      (ChowMotive.tateTwist (SchemeOverField.point k) m ⊗
        ChowMotive.tateTwist (SchemeOverField.point k) n).p = f := sorry

/-- The inverse point-product unitor as a morphism from the sum-index twist to the tensor
product of the two point Tate twists. -/
noncomputable def tensorInv (k : Type u) [Field k] (m n : ℤ) :
    ChowMotive.tateTwist (SchemeOverField.point k) (m + n) ⟶
      ChowMotive.tateTwist (SchemeOverField.point k) m ⊗
        ChowMotive.tateTwist (SchemeOverField.point k) n where
  f := Correspondence.GradedCategory.homOfDegreeZero rfl
    (Correspondence.rationalGraphIso
      (ChowMotive.tateTwist (SchemeOverField.point k) (m + n)).X.1
      (ChowMotive.tateTwist (SchemeOverField.point k) m ⊗
        ChowMotive.tateTwist (SchemeOverField.point k) n).X.1
      (Correspondence.GradedCategory.leftUnitorSchemeIso
        (Correspondence.GradedCategory.ofScheme (SchemeOverField.point k) n)).symm)
  comm := tensorInv_comm k m n

/-- The underlying graded correspondence of `tensorInv` is the rational graph of the
inverse point-product unitor. -/
theorem tensorInv_f (k : Type u) [Field k] (m n : ℤ) :
    (tensorInv k m n).f =
      (Correspondence.GradedCategory.homOfDegreeZero rfl
        (Correspondence.rationalGraphIso
          (ChowMotive.tateTwist (SchemeOverField.point k) (m + n)).X.1
          (ChowMotive.tateTwist (SchemeOverField.point k) m ⊗
            ChowMotive.tateTwist (SchemeOverField.point k) n).X.1
          (Correspondence.GradedCategory.leftUnitorSchemeIso
            (Correspondence.GradedCategory.ofScheme (SchemeOverField.point k) n)).symm) :
        (ChowMotive.tateTwist (SchemeOverField.point k) (m + n)).X ⟶
          (ChowMotive.tateTwist (SchemeOverField.point k) m ⊗
            ChowMotive.tateTwist (SchemeOverField.point k) n).X) := sorry

/-- The point-product maps compose to the identity on the tensor of point Tate twists. -/
theorem tensorIso_hom_inv_id (k : Type u) [Field k] (m n : ℤ) :
    tensorHom k m n ≫ tensorInv k m n = 𝟙 _ := sorry

/-- The point-product maps compose to the identity on the sum-index point Tate twist. -/
theorem tensorIso_inv_hom_id (k : Type u) [Field k] (m n : ℤ) :
    tensorInv k m n ≫ tensorHom k m n = 𝟙 _ := sorry

/-- Tensoring point Tate twists adds their integral indices. -/
noncomputable def tensorIso (k : Type u) [Field k] (m n : ℤ) :
    ChowMotive.tateTwist (SchemeOverField.point k) m ⊗
        ChowMotive.tateTwist (SchemeOverField.point k) n ≅
      ChowMotive.tateTwist (SchemeOverField.point k) (m + n) where
  hom := tensorHom k m n
  inv := tensorInv k m n
  hom_inv_id := tensorIso_hom_inv_id k m n
  inv_hom_id := tensorIso_inv_hom_id k m n

/-- The underlying hom of `tensorIso` is the rational graph of the point-product unitor. -/
theorem tensorIso_hom_f (k : Type u) [Field k] (m n : ℤ) :
    (tensorIso k m n).hom.f =
      (Correspondence.GradedCategory.homOfDegreeZero rfl
        (Correspondence.rationalGraphIso
          (ChowMotive.tateTwist (SchemeOverField.point k) m ⊗
            ChowMotive.tateTwist (SchemeOverField.point k) n).X.1
          (ChowMotive.tateTwist (SchemeOverField.point k) (m + n)).X.1
          (Correspondence.GradedCategory.leftUnitorSchemeIso
            (Correspondence.GradedCategory.ofScheme (SchemeOverField.point k) n))) :
        (ChowMotive.tateTwist (SchemeOverField.point k) m ⊗
            ChowMotive.tateTwist (SchemeOverField.point k) n).X ⟶
          (ChowMotive.tateTwist (SchemeOverField.point k) (m + n)).X) := sorry

/-- The point Tate twist of index zero is the tensor unit. -/
noncomputable def zeroIso (k : Type u) [Field k] :
    ChowMotive.tateTwist (SchemeOverField.point k) 0 ≅
      𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :=
  Iso.refl _

/-- The comparison `zeroIso` is the identity isomorphism. -/
theorem zeroIso_def (k : Type u) [Field k] : zeroIso k = Iso.refl _ := sorry

/-- The point Tate twist of index `-n` is an explicit right tensor inverse to the twist
of index `n`. -/
noncomputable def rightInverseIso (k : Type u) [Field k] (n : ℤ) :
    ChowMotive.tateTwist (SchemeOverField.point k) n ⊗
        ChowMotive.tateTwist (SchemeOverField.point k) (-n) ≅
      𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :=
  tensorIso k n (-n) ≪≫
    eqToIso (congrArg (ChowMotive.tateTwist (SchemeOverField.point k)) (add_neg_cancel n)) ≪≫
      zeroIso k

/-- The right-inverse comparison is tensor addition followed by normalization of index zero. -/
theorem rightInverseIso_def (k : Type u) [Field k] (n : ℤ) :
    rightInverseIso k n =
      tensorIso k n (-n) ≪≫
        eqToIso
          (congrArg (ChowMotive.tateTwist (SchemeOverField.point k)) (add_neg_cancel n)) ≪≫
        zeroIso k := sorry

/-- The point Tate twist of index `-n` is an explicit left tensor inverse to the twist
of index `n`. -/
noncomputable def leftInverseIso (k : Type u) [Field k] (n : ℤ) :
    ChowMotive.tateTwist (SchemeOverField.point k) (-n) ⊗
        ChowMotive.tateTwist (SchemeOverField.point k) n ≅
      𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :=
  tensorIso k (-n) n ≪≫
    eqToIso (congrArg (ChowMotive.tateTwist (SchemeOverField.point k)) (neg_add_cancel n)) ≪≫
      zeroIso k

/-- The left-inverse comparison is tensor addition followed by normalization of index zero. -/
theorem leftInverseIso_def (k : Type u) [Field k] (n : ℤ) :
    leftInverseIso k n =
      tensorIso k (-n) n ≪≫
        eqToIso
          (congrArg (ChowMotive.tateTwist (SchemeOverField.point k)) (neg_add_cancel n)) ≪≫
        zeroIso k := sorry

/-- Every integral point Tate twist is tensor-invertible, with inverse the twist of the
opposite index. -/
instance instIsInvertibleObject (k : Type u) [Field k] (n : ℤ) :
    MonoidalCategory.isInvertibleObject
      (ChowMotive.tateTwist (SchemeOverField.point k) n) := sorry

end ChowMotive.Tate
