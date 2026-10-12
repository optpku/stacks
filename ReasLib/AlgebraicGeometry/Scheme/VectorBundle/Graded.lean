/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cone.Basic
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.SymmetricPower

/-!
# Graded vector bundles over a scheme

A vector bundle is presented as an affine cone whose homogeneous pieces are canonically the
symmetric powers of its degree-one piece. Morphisms are the grading-preserving morphisms of the
underlying cones.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

/-- A vector bundle over `S`, consisting of an affine graded cone together with canonical
symmetric-power comparisons that are isomorphisms in every degree. -/
structure VectorBundleOver where
  /-- The affine graded cone underlying the vector bundle. -/
  cone : ConeOver S
  /-- The comparison from the symmetric power of degree one to each homogeneous piece. -/
  symmetricPowerToDegree :
    ∀ n : ℕ, RingedSpace.SymmetricPower.sheaf
      (cone.pushforwardGrading.degreePiece 1) n ⟶ cone.pushforwardGrading.degreePiece n
  /-- The comparisons are induced by iterated homogeneous multiplication. -/
  symmetricPowerToDegree_isCanonical :
    GradedQcAlgebra.IsSymmetricPowerComparison cone.pushforwardGrading symmetricPowerToDegree
  /-- Every symmetric-power comparison is an isomorphism. -/
  symmetricPowerToDegree_isIso : ∀ n : ℕ, IsIso (symmetricPowerToDegree n)

namespace VectorBundleOver

/-- Construct a vector bundle from an affine graded cone whose canonical symmetric-power
comparisons are isomorphisms in every degree. -/
def ofCone (cone : ConeOver S)
    (symmetricPowerToDegree :
      ∀ n : ℕ, RingedSpace.SymmetricPower.sheaf
        (cone.pushforwardGrading.degreePiece 1) n ⟶ cone.pushforwardGrading.degreePiece n)
    (symmetricPowerToDegree_isCanonical :
      GradedQcAlgebra.IsSymmetricPowerComparison cone.pushforwardGrading
        symmetricPowerToDegree)
    (symmetricPowerToDegree_isIso : ∀ n : ℕ, IsIso (symmetricPowerToDegree n)) :
    VectorBundleOver S where
  cone := cone
  symmetricPowerToDegree := symmetricPowerToDegree
  symmetricPowerToDegree_isCanonical := symmetricPowerToDegree_isCanonical
  symmetricPowerToDegree_isIso := symmetricPowerToDegree_isIso

/-- The total space of a vector bundle. -/
abbrev V (E : VectorBundleOver S) : Scheme.{u} :=
  E.cone.C

/-- The projection of a vector bundle to its base. -/
abbrev π (E : VectorBundleOver S) : E.V ⟶ S :=
  E.cone.π

/-- The grading of the pushforward structure algebra. -/
abbrev pushforwardGrading (E : VectorBundleOver S) : GradedQcAlgebra S :=
  E.cone.pushforwardGrading

/-- The identification of the chosen graded algebra with the actual pushforward structure
algebra. -/
abbrev pushforwardAlgebraIso (E : VectorBundleOver S) :
    (QcAlgebraUnder.forget S).obj E.pushforwardGrading.algebra ≅
      Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap E.π.toShHom) :=
  E.cone.pushforwardAlgebraIso

/-- The projection of a vector bundle is affine. -/
theorem isAffineHom (E : VectorBundleOver S) : IsAffineHom E.π :=
  ConeOver.isAffineHom S E.cone

/-- The complete specification of the affine grading and canonical symmetric-power
comparisons of a vector bundle. -/
theorem spec (E : VectorBundleOver S) :
    IsAffineHom E.π ∧
      (∀ {U V : (Opens S)ᵒᵖ} (f : U ⟶ V),
        ((E.pushforwardGrading.degreePiece 0).val.map f).hom
            (E.pushforwardGrading.one U) = E.pushforwardGrading.one V) ∧
      (∀ {U V : (Opens S)ᵒᵖ} (f : U ⟶ V) (n m : ℕ)
        (a : (E.pushforwardGrading.degreePiece n).val.obj U)
        (b : (E.pushforwardGrading.degreePiece m).val.obj U),
        ((E.pushforwardGrading.degreePiece (n + m)).val.map f).hom
            (E.pushforwardGrading.mul U n m a b) =
          E.pushforwardGrading.mul V n m
            (((E.pushforwardGrading.degreePiece n).val.map f).hom a)
            (((E.pushforwardGrading.degreePiece m).val.map f).hom b)) ∧
      (∀ (U : (Opens S)ᵒᵖ) (i j k : ℕ)
        (a : (E.pushforwardGrading.degreePiece i).val.obj U)
        (b : (E.pushforwardGrading.degreePiece j).val.obj U)
        (c : (E.pushforwardGrading.degreePiece k).val.obj U),
        HEq
          (E.pushforwardGrading.mul U (i + j) k
            (E.pushforwardGrading.mul U i j a b) c)
          (E.pushforwardGrading.mul U i (j + k) a
            (E.pushforwardGrading.mul U j k b c))) ∧
      (∀ (U : (Opens S)ᵒᵖ) (n : ℕ)
        (a : (E.pushforwardGrading.degreePiece n).val.obj U),
        HEq (E.pushforwardGrading.mul U 0 n (E.pushforwardGrading.one U) a) a) ∧
      (∀ (U : (Opens S)ᵒᵖ) (n : ℕ)
        (a : (E.pushforwardGrading.degreePiece n).val.obj U),
        HEq (E.pushforwardGrading.mul U n 0 a (E.pushforwardGrading.one U)) a) ∧
      (∃ degreeZeroIso : E.pushforwardGrading.degreePiece 0 ≅
          SheafOfModules.unit S.ringCatSheaf,
        degreeZeroIso = E.pushforwardGrading.degreeZeroIso) ∧
      (∀ n : ℕ,
        E.pushforwardGrading.degreePieceToUnderlying n ≫
            E.pushforwardGrading.underlyingToDegreePiece n =
          𝟙 (E.pushforwardGrading.degreePiece n)) ∧
      (∀ {n m : ℕ}, n ≠ m →
        E.pushforwardGrading.degreePieceToUnderlying n ≫
          E.pushforwardGrading.underlyingToDegreePiece m = 0) ∧
      (∀ (U : (Opens S)ᵒᵖ)
        (a : (QcAlgebraUnder.underlyingModule S
          E.pushforwardGrading.algebra).val.obj U),
        ∃ s : Finset ℕ,
          a = Finset.sum s fun n ↦
            (((E.pushforwardGrading.degreePieceToUnderlying n).val.app U).hom)
              ((((E.pushforwardGrading.underlyingToDegreePiece n).val.app U).hom) a)) ∧
      GradedQcAlgebra.algebraRespectsGradingProp S E.pushforwardGrading ∧
      GradedQcAlgebra.degreeZeroUnitCompatibleProp S E.pushforwardGrading ∧
      GradedQcAlgebra.IsSymmetricPowerComparison E.pushforwardGrading
        E.symmetricPowerToDegree ∧
      (∀ n : ℕ, IsIso (E.symmetricPowerToDegree n)) ∧
      (∃ pushforwardAlgebraIso :
          (QcAlgebraUnder.forget S).obj E.pushforwardGrading.algebra ≅
            Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap E.π.toShHom),
        pushforwardAlgebraIso = E.pushforwardAlgebraIso) := by
  rcases E.cone.spec with
    ⟨h_affine, h_one, h_mul, h_assoc, h_one_mul, h_mul_one, h_zero, h_split,
      h_orthogonal, h_sum, h_respects, h_unit, h_pushforward⟩
  exact ⟨h_affine, h_one, h_mul, h_assoc, h_one_mul, h_mul_one, h_zero, h_split,
    h_orthogonal, h_sum, h_respects, h_unit, E.symmetricPowerToDegree_isCanonical,
    E.symmetricPowerToDegree_isIso, h_pushforward⟩

/-- The chosen quasi-coherent algebra underlying a vector bundle. -/
abbrev chosenAlgebra (E : VectorBundleOver S) : S.QcAlgebraUnder :=
  E.pushforwardGrading.algebra

/-- The inclusion of a homogeneous piece into the underlying graded algebra. -/
abbrev degreePieceToUnderlyingMap (E : VectorBundleOver S) (n : ℕ) :
    E.pushforwardGrading.degreePiece n ⟶ QcAlgebraUnder.underlyingModule S E.chosenAlgebra :=
  E.pushforwardGrading.degreePieceToUnderlying n

/-- The projection from the underlying graded algebra to a homogeneous piece. -/
abbrev underlyingToDegreePieceMap (E : VectorBundleOver S) (n : ℕ) :
    QcAlgebraUnder.underlyingModule S E.chosenAlgebra ⟶ E.pushforwardGrading.degreePiece n :=
  E.pushforwardGrading.underlyingToDegreePiece n

/-- The identification of the degree-zero piece with the structure sheaf. -/
abbrev degreeZeroIso (E : VectorBundleOver S) :
    E.pushforwardGrading.degreePiece 0 ≅ SheafOfModules.unit S.ringCatSheaf :=
  E.pushforwardGrading.degreeZeroIso

/-- The forward map of the degree-zero identification. -/
abbrev degreeZeroHom (E : VectorBundleOver S) :
    E.pushforwardGrading.degreePiece 0 ⟶ SheafOfModules.unit S.ringCatSheaf :=
  E.degreeZeroIso.hom

/-- The comparison from the chosen algebra to the actual pushforward structure algebra. -/
abbrev pushforwardAlgebraHom (E : VectorBundleOver S) :
    (QcAlgebraUnder.forget S).obj E.chosenAlgebra ⟶
      Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap E.π.toShHom) :=
  E.pushforwardAlgebraIso.hom

end VectorBundleOver

/-- Compatibility of a morphism over `S` with the gradings on the underlying affine cones. -/
abbrev vectorBundleHomCompatibleWithGrading
    {E E' : VectorBundleOver S} (hom : E.V ⟶ E'.V) (overBase : hom ≫ E'.π = E.π) :
    Prop :=
  coneHomCompatibleWithGrading S hom overBase

/-- A morphism of vector bundles over `S`, represented by a grading-preserving morphism of
their underlying affine cones. -/
abbrev VectorBundleHom (E E' : VectorBundleOver S) : Type u :=
  ConeHom S E.cone E'.cone

namespace VectorBundleHom

/-- The complete specification of a vector-bundle morphism. -/
theorem spec {E E' : VectorBundleOver S} (f : VectorBundleHom S E E') :
    (f.hom ≫ E'.π = E.π) ∧
      vectorBundleHomCompatibleWithGrading S f.hom f.overBase := by
  exact ConeHom.spec S f

/-- The underlying scheme morphism of a vector-bundle morphism. -/
def toSchemeHom {E E' : VectorBundleOver S} (f : VectorBundleHom S E E') : E.V ⟶ E'.V :=
  ConeHom.toSchemeHom S f

end VectorBundleHom

end AlgebraicGeometry.Scheme
