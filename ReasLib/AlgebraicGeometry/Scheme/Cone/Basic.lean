/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.RingedSpace.Definition
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Graded

/-!
# Cones over schemes

This file bundles a cone over a fixed scheme and its grading-preserving morphisms.  The affine
condition and all grading data remain explicit rather than being registered as instances.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

/-- A cone over `S`, presented by an affine total space and an explicit grading of its actual
pushforward structure algebra. -/
structure ConeOver where
  /-- The total space of the cone. -/
  C : Scheme.{u}
  /-- The structure morphism `π : C ⟶ S`. -/
  π : C ⟶ S
  /-- The structure morphism is affine. -/
  affine : IsAffineHom π
  /-- The explicit grading of the chosen pushforward algebra. -/
  pushforwardGrading : GradedQcAlgebra S
  /-- The chosen algebra is identified with the actual pushforward structure algebra. -/
  pushforwardAlgebraIso :
    (QcAlgebraUnder.forget S).obj pushforwardGrading.algebra ≅
      Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap π.toShHom)

namespace ConeOver

/-- The structure morphism of a cone is affine. -/
theorem isAffineHom (X : ConeOver S) : IsAffineHom X.π :=
  X.affine

/-- The chosen degree-zero identification attached to a cone. -/
def degreeZeroIso (X : ConeOver S) :
    X.pushforwardGrading.degreePiece 0 ≅ SheafOfModules.unit S.ringCatSheaf :=
  X.pushforwardGrading.degreeZeroIso

end ConeOver

/-- The canonical pullback on actual pushforward structure algebras induced by a morphism over
`S`. -/
def inducedConePushforwardPullback {X X' : ConeOver S}
    (hom : X.C ⟶ X'.C) (overBase : hom ≫ X'.π = X.π) :
    Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap X'.π.toShHom) ⟶
      Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap X.π.toShHom) :=
  overBase ▸
    Under.homMk
      ((TopCat.Sheaf.pushforward CommRingCat.{u} X'.π.1.base).map
        (RingedSpace.Hom.commRingSheafPushforwardMap hom.toShHom))
      rfl

namespace ConeOver

/-- The pullback on the chosen quasi-coherent algebras, transported through their
identifications with the actual pushforward structure algebras. -/
def chosenAlgebraPullback {X X' : ConeOver S}
    (hom : X.C ⟶ X'.C) (overBase : hom ≫ X'.π = X.π) :
    X'.pushforwardGrading.algebra ⟶ X.pushforwardGrading.algebra :=
  ObjectProperty.homMk
    (X'.pushforwardAlgebraIso.hom ≫
      inducedConePushforwardPullback S hom overBase ≫ X.pushforwardAlgebraIso.inv)

/-- The complete specification of a cone over `S`. -/
theorem spec (X : ConeOver S) :
    IsAffineHom X.π ∧
      (∀ {U V : (Opens S)ᵒᵖ} (f : U ⟶ V),
        ((X.pushforwardGrading.degreePiece 0).val.map f).hom
            (X.pushforwardGrading.one U) = X.pushforwardGrading.one V) ∧
      (∀ {U V : (Opens S)ᵒᵖ} (f : U ⟶ V) (n m : ℕ)
        (a : (X.pushforwardGrading.degreePiece n).val.obj U)
        (b : (X.pushforwardGrading.degreePiece m).val.obj U),
        ((X.pushforwardGrading.degreePiece (n + m)).val.map f).hom
            (X.pushforwardGrading.mul U n m a b) =
          X.pushforwardGrading.mul V n m
            (((X.pushforwardGrading.degreePiece n).val.map f).hom a)
            (((X.pushforwardGrading.degreePiece m).val.map f).hom b)) ∧
      (∀ (U : (Opens S)ᵒᵖ) (i j k : ℕ)
        (a : (X.pushforwardGrading.degreePiece i).val.obj U)
        (b : (X.pushforwardGrading.degreePiece j).val.obj U)
        (c : (X.pushforwardGrading.degreePiece k).val.obj U),
        HEq
          (X.pushforwardGrading.mul U (i + j) k
            (X.pushforwardGrading.mul U i j a b) c)
          (X.pushforwardGrading.mul U i (j + k) a
            (X.pushforwardGrading.mul U j k b c))) ∧
      (∀ (U : (Opens S)ᵒᵖ) (n : ℕ)
        (a : (X.pushforwardGrading.degreePiece n).val.obj U),
        HEq (X.pushforwardGrading.mul U 0 n (X.pushforwardGrading.one U) a) a) ∧
      (∀ (U : (Opens S)ᵒᵖ) (n : ℕ)
        (a : (X.pushforwardGrading.degreePiece n).val.obj U),
        HEq (X.pushforwardGrading.mul U n 0 a (X.pushforwardGrading.one U)) a) ∧
      (∃ degreeZeroIso : X.pushforwardGrading.degreePiece 0 ≅
          SheafOfModules.unit S.ringCatSheaf,
        degreeZeroIso = X.pushforwardGrading.degreeZeroIso) ∧
      (∀ n : ℕ,
        X.pushforwardGrading.degreePieceToUnderlying n ≫
            X.pushforwardGrading.underlyingToDegreePiece n =
          𝟙 (X.pushforwardGrading.degreePiece n)) ∧
      (∀ {n m : ℕ}, n ≠ m →
        X.pushforwardGrading.degreePieceToUnderlying n ≫
          X.pushforwardGrading.underlyingToDegreePiece m = 0) ∧
      (∀ (U : (Opens S)ᵒᵖ)
        (a : (QcAlgebraUnder.underlyingModule S
          X.pushforwardGrading.algebra).val.obj U),
        ∃ s : Finset ℕ,
          a = Finset.sum s fun n ↦
            (((X.pushforwardGrading.degreePieceToUnderlying n).val.app U).hom)
              ((((X.pushforwardGrading.underlyingToDegreePiece n).val.app U).hom) a)) ∧
      GradedQcAlgebra.algebraRespectsGradingProp S X.pushforwardGrading ∧
      GradedQcAlgebra.degreeZeroUnitCompatibleProp S X.pushforwardGrading ∧
      (∃ pushforwardAlgebraIso :
          (QcAlgebraUnder.forget S).obj X.pushforwardGrading.algebra ≅
            Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap X.π.toShHom),
        pushforwardAlgebraIso = X.pushforwardAlgebraIso) := by
  exact ⟨X.affine, X.pushforwardGrading.map_one, X.pushforwardGrading.map_mul,
    X.pushforwardGrading.mul_assoc, X.pushforwardGrading.one_mul,
    X.pushforwardGrading.mul_one, ⟨X.pushforwardGrading.degreeZeroIso, rfl⟩,
    X.pushforwardGrading.degreePiece_split, X.pushforwardGrading.degreePiece_orthogonal,
    X.pushforwardGrading.underlying_eq_sum_components,
    X.pushforwardGrading.algebra_respects_grading,
    X.pushforwardGrading.degree_zero_unit_compatible, ⟨X.pushforwardAlgebraIso, rfl⟩⟩

end ConeOver

/-- The canonical pullback associated to a morphism over the base preserves the chosen
gradings. -/
def coneHomCompatibleWithGrading {X X' : ConeOver S}
    (hom : X.C ⟶ X'.C) (overBase : hom ≫ X'.π = X.π) : Prop :=
  GradedQcAlgebra.IsGradedHom S (ConeOver.chosenAlgebraPullback S hom overBase)

/-- A morphism of cones over `S`. -/
structure ConeHom (X X' : ConeOver S) where
  /-- The underlying morphism of total spaces. -/
  hom : X.C ⟶ X'.C
  /-- The morphism lies over the fixed base scheme. -/
  overBase : hom ≫ X'.π = X.π
  /-- The induced contravariant algebra map preserves the explicit gradings. -/
  compatibleWithGrading : coneHomCompatibleWithGrading S hom overBase

namespace ConeHom

/-- The complete specification of a morphism of cones over `S`. -/
theorem spec {X X' : ConeOver S} (f : ConeHom S X X') :
    (f.hom ≫ X'.π = X.π) ∧
      coneHomCompatibleWithGrading S f.hom f.overBase := by
  exact ⟨f.overBase, f.compatibleWithGrading⟩

/-- The underlying scheme morphism of a cone morphism. -/
def toSchemeHom {X X' : ConeOver S} (f : ConeHom S X X') : X.C ⟶ X'.C :=
  f.hom

end ConeHom

end AlgebraicGeometry.Scheme
