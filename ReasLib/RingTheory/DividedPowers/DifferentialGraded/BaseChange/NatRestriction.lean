module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.NatRestriction.Homology
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.BaseChange

/-!
# Scalar extension of the natural complex of a divided-power chain DGA

An explicit base-change model identifies the scalar extension of the source natural complex
with the natural complex underlying the model.  The categorical owner is
`ModuleCat.extendScalars (algebraMap R S)`: unlike tensoring inside `ModuleCat R`, this functor
lands in `ModuleCat S`, so its complex can be compared directly with the target complex.

The degreewise identification is normalized to the ordinary tensor product before applying the
recorded `BaseChange.pieceIso`.  The resulting complex and homology isomorphisms are natural in
the supplied base-change model and never choose a model from `nonemptyBaseChange`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe uR u

namespace DividedPowerChainAlgebra.BaseChange.NatRestriction

variable {R : Type uR} {S : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable {A : DividedPowerChainAlgebra.{uR, u} R}

/-- Tag 09PL and Tag 09PQ: the natural complex of a divided-power chain DGA after categorical
extension of scalars from `R` to `S`. -/
@[stacks 09PL "scalar-extended natural complex",
  stacks 09PQ "scalar-extended natural complex"]
abbrev tensorComplex (A : DividedPowerChainAlgebra.{uR, u} R) :
    ChainComplex (ModuleCat.{u} S) ℕ :=
  ((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj A.toChainDGAlgebra.natRestriction

/-- The degree-`n` object of the categorical scalar extension is canonically the ordinary
tensor-product module `S ⊗[R] A_n`. -/
@[stacks 09PL "degreewise tensor normalization",
  stacks 09PQ "degreewise tensor normalization"]
noncomputable def tensorPieceIso
    (A : DividedPowerChainAlgebra.{uR, u} R) (n : ℕ) :
    (tensorComplex (S := S) A).X n ≅
      ModuleCat.of S (S ⊗[R] A.toChainDGAlgebra.nonnegativePiece n) :=
  (ModuleCat.extendScalars (algebraMap R S)).mapIso
      (A.toChainDGAlgebra.natRestrictionXIso n) ≪≫
    ModuleCat.ExtendScalars.tensorIso (R := R) (S := S)
      (A.toChainDGAlgebra.toChainComplex.X (n : ℤ))

/-- The pure tensor `s ⊗ₜ x` as an element of the categorical scalar-extension complex. -/
noncomputable def pureTensor
    (A : DividedPowerChainAlgebra.{uR, u} R) (n : ℕ) (s : S)
    (x : A.toChainDGAlgebra.nonnegativePiece n) :
    (tensorComplex (S := S) A).X n :=
  (tensorPieceIso (S := S) A n).inv (s ⊗ₜ[R] x)

/-- Tensor normalization sends the categorical pure tensor to the corresponding ordinary pure
tensor. -/
@[simp]
theorem tensorPieceIso_hom_pureTensor
    (A : DividedPowerChainAlgebra.{uR, u} R) (n : ℕ) (s : S)
    (x : A.toChainDGAlgebra.nonnegativePiece n) :
    (tensorPieceIso (S := S) A n).hom (pureTensor A n s x) = s ⊗ₜ[R] x := sorry

/-- The differential of the scalar-extension complex acts on the second factor of a pure
tensor. -/
@[simp]
theorem d_pureTensor
    (A : DividedPowerChainAlgebra.{uR, u} R) (n : ℕ+) (s : S)
    (x : A.toChainDGAlgebra.nonnegativePiece n) :
    (tensorComplex (S := S) A).d n ((n : ℕ) - 1) (pureTensor A n s x) =
      pureTensor A ((n : ℕ) - 1) s
        (A.toChainDGAlgebra.nonnegativeDifferential n x) := sorry

/-- The degreewise `ModuleCat S` isomorphism supplied by an explicit base-change model.  It
first normalizes categorical scalar extension to `S ⊗[R] A_n`, applies `X.pieceIso n`, and then
returns to the natural restriction of the target chain DGA. -/
@[stacks 09PL "degreewise scalar-extension comparison",
  stacks 09PQ "degreewise scalar-extension comparison"]
noncomputable def pieceModuleIso
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ) :
    (tensorComplex (S := S) A).X n ≅
      X.algebra.toChainDGAlgebra.natRestriction.X n :=
  tensorPieceIso (S := S) A n ≪≫
    (X.pieceIso n).toModuleIso ≪≫
      (X.algebra.toChainDGAlgebra.natRestrictionXIso n).symm

/-- The forward degreewise comparison is explicitly `X.pieceIso n` after tensor normalization
and the target restriction identification. -/
@[simp]
theorem pieceModuleIso_hom_apply
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ)
    (z : (tensorComplex (S := S) A).X n) :
    (X.algebra.toChainDGAlgebra.natRestrictionXIso n).hom
        ((pieceModuleIso X n).hom z) =
      X.pieceIso n ((tensorPieceIso (S := S) A n).hom z) := sorry

/-- The inverse degreewise comparison is explicitly the inverse of `X.pieceIso n` after the
target restriction and tensor normalizations. -/
@[simp]
theorem pieceModuleIso_inv_apply
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ)
    (y : X.algebra.toChainDGAlgebra.natRestriction.X n) :
    (tensorPieceIso (S := S) A n).hom ((pieceModuleIso X n).inv y) =
      (X.pieceIso n).symm
        ((X.algebra.toChainDGAlgebra.natRestrictionXIso n).hom y) := sorry

/-- On a pure tensor, the forward degreewise comparison is the recorded base-change
identification. -/
@[simp]
theorem pieceModuleIso_hom_pureTensor
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ) (s : S)
    (x : A.toChainDGAlgebra.nonnegativePiece n) :
    (pieceModuleIso X n).hom (pureTensor A n s x) =
      (X.algebra.toChainDGAlgebra.natRestrictionXIso n).inv
        (X.pieceIso n (s ⊗ₜ[R] x)) := sorry

/-- Applying the inverse comparison to a model piece recovers its tensor representative. -/
@[simp]
theorem pieceModuleIso_inv_piece
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ)
    (z : S ⊗[R] A.toChainDGAlgebra.nonnegativePiece n) :
    (pieceModuleIso X n).inv
        ((X.algebra.toChainDGAlgebra.natRestrictionXIso n).inv (X.pieceIso n z)) =
      (tensorPieceIso (S := S) A n).inv z := sorry

/-- The forward degreewise identifications commute with every differential of the natural
complexes. -/
theorem pieceModuleIso_hom_d
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (pieceModuleIso X i).hom ≫
        X.algebra.toChainDGAlgebra.natRestriction.d i j =
      (tensorComplex (S := S) A).d i j ≫ (pieceModuleIso X j).hom := sorry

/-- Tag 09PL and Tag 09PQ: the scalar-extended source natural complex is canonically isomorphic
to the natural complex of any supplied base-change model. -/
@[stacks 09PL "natural-complex base-change comparison",
  stacks 09PQ "natural-complex base-change comparison"]
noncomputable def complexIso
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) :
    tensorComplex (S := S) A ≅
      X.algebra.toChainDGAlgebra.natRestriction :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ pieceModuleIso X n) (pieceModuleIso_hom_d X)

/-- The forward chain map of the natural-complex base-change isomorphism. -/
noncomputable def complexHom
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) :
    tensorComplex (S := S) A ⟶
      X.algebra.toChainDGAlgebra.natRestriction :=
  (complexIso X).hom

/-- The inverse chain map of the natural-complex base-change isomorphism. -/
noncomputable def complexInv
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) :
    X.algebra.toChainDGAlgebra.natRestriction ⟶
      tensorComplex (S := S) A :=
  (complexIso X).inv

/-- The degree-`n` component of the whole-complex isomorphism is `pieceModuleIso X n`. -/
@[simp]
theorem complexIso_app
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ) :
    HomologicalComplex.Hom.isoApp (complexIso X) n = pieceModuleIso X n := sorry

/-- The forward morphism of `complexIso` is `complexHom`. -/
@[simp]
theorem complexIso_hom
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) :
    (complexIso X).hom = complexHom X := sorry

/-- The inverse morphism of `complexIso` is `complexInv`. -/
@[simp]
theorem complexIso_inv
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) :
    (complexIso X).inv = complexInv X := sorry

/-- The degree-`n` component of the forward chain map is the forward degreewise comparison. -/
@[simp]
theorem complexHom_f
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ) :
    (complexHom X).f n = (pieceModuleIso X n).hom := sorry

/-- The degree-`n` component of the inverse chain map is the inverse degreewise comparison. -/
@[simp]
theorem complexInv_f
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ) :
    (complexInv X).f n = (pieceModuleIso X n).inv := sorry

/-- The forward chain map has the recorded `X.pieceIso` formula on every pure tensor. -/
@[simp]
theorem complexHom_pureTensor
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ) (s : S)
    (x : A.toChainDGAlgebra.nonnegativePiece n) :
    (complexHom X).f n (pureTensor A n s x) =
      (X.algebra.toChainDGAlgebra.natRestrictionXIso n).inv
        (X.pieceIso n (s ⊗ₜ[R] x)) := sorry

/-- The inverse chain map sends a model piece to its normalized tensor representative. -/
@[simp]
theorem complexInv_piece
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ)
    (z : S ⊗[R] A.toChainDGAlgebra.nonnegativePiece n) :
    (complexInv X).f n
        ((X.algebra.toChainDGAlgebra.natRestrictionXIso n).inv (X.pieceIso n z)) =
      (tensorPieceIso (S := S) A n).inv z := sorry

/-- The forward chain map commutes with the differentials in every related pair of degrees. -/
theorem complexHom_d
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (complexHom X).f i ≫ X.algebra.toChainDGAlgebra.natRestriction.d i j =
      (tensorComplex (S := S) A).d i j ≫ (complexHom X).f j := sorry

/-- The inverse chain map commutes with the differentials in every related pair of degrees. -/
theorem complexInv_d
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (complexInv X).f i ≫ (tensorComplex (S := S) A).d i j =
      X.algebra.toChainDGAlgebra.natRestriction.d i j ≫ (complexInv X).f j := sorry

/-- Tag 09PQ: homology of the scalar-extended natural complex is canonically the homology of
the natural complex underlying a supplied base-change model. -/
@[stacks 09PL "homology of a scalar-extended natural complex",
  stacks 09PQ "homology of a scalar-extended natural complex"]
noncomputable def homologyIso
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ) :
    (tensorComplex (S := S) A).homology n ≅
      X.algebra.toChainDGAlgebra.natRestriction.homology n :=
  HomologicalComplex.homologyMapIso (complexIso X) n

/-- Tag 09PQ: homology of the scalar-extended natural complex is canonically the integer-graded
homology of any supplied nonnegative base-change model. -/
@[stacks 09PQ "integer homology of a scalar-extended natural complex"]
noncomputable def integerHomologyIso
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ) :
    (tensorComplex (S := S) A).homology n ≅
      X.algebra.toChainDGAlgebra.homology (n : ℤ) :=
  homologyIso X n ≪≫ X.algebra.toChainDGAlgebra.natRestrictionHomologyIso n

/-- The integer-homology comparison is the composite of the explicit base-change complex
comparison and the canonical comparison from natural to integer degrees. -/
theorem integerHomologyIso_hom
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ) :
    (integerHomologyIso X n).hom =
      (homologyIso X n).hom ≫
        (X.algebra.toChainDGAlgebra.natRestrictionHomologyIso n).hom := sorry

/-- The forward homology comparison is induced by `complexHom`. -/
@[simp]
theorem homologyIso_hom
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ) :
    (homologyIso X n).hom = HomologicalComplex.homologyMap (complexHom X) n := sorry

/-- The inverse homology comparison is induced by `complexInv`. -/
@[simp]
theorem homologyIso_inv
    (X : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ) :
    (homologyIso X n).inv = HomologicalComplex.homologyMap (complexInv X) n := sorry

/-- Restricting the canonical divided-power chain-DGA comparison gives the canonical
natural-complex isomorphism between two supplied base-change models. -/
@[stacks 09PL "natural-complex comparison of base-change models",
  stacks 09PQ "natural-complex comparison of base-change models"]
def comparisonComplexIso
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A) :
    X.algebra.toChainDGAlgebra.natRestriction ≅
      Y.algebra.toChainDGAlgebra.natRestriction :=
  ((DividedPowerChainAlgebra.forget S ⋙
      ChainDGAlgebra.natRestrictionFunctor S).mapIso (X.comparisonIso Y))

/-- The forward map of the model-comparison complex isomorphism is the natural restriction of
the canonical chain-DGA comparison. -/
@[simp]
theorem comparisonComplexIso_hom
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A) :
    (comparisonComplexIso X Y).hom =
      (X.chainComparison Y).toChainHom.natRestriction := sorry

/-- The inverse map of the model-comparison complex isomorphism is the natural restriction of
the reverse canonical chain-DGA comparison. -/
@[simp]
theorem comparisonComplexIso_inv
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A) :
    (comparisonComplexIso X Y).inv =
      (Y.chainComparison X).toChainHom.natRestriction := sorry

/-- The forward model comparison acts in degree `n` by the canonical homogeneous comparison. -/
@[simp]
theorem comparisonComplexIso_hom_f
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ) :
    (comparisonComplexIso X Y).hom.f n =
      (X.algebra.toChainDGAlgebra.natRestrictionXIso n).hom ≫
        (X.comparisonPiece Y n).toModuleIso.hom ≫
          (Y.algebra.toChainDGAlgebra.natRestrictionXIso n).inv := sorry

/-- The scalar-extension complex isomorphisms are natural under canonical comparison of two
supplied base-change models. -/
theorem complexIso_naturality
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A) :
    (complexIso X).trans (comparisonComplexIso X Y) = complexIso Y := sorry

/-- Forward scalar-extension chain maps commute with canonical comparison of base-change
models. -/
theorem complexHom_naturality
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A) :
    complexHom X ≫ (X.chainComparison Y).toChainHom.natRestriction =
      complexHom Y := sorry

/-- Inverse scalar-extension chain maps commute with canonical comparison of base-change
models. -/
theorem complexInv_naturality
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A) :
    (X.chainComparison Y).toChainHom.natRestriction ≫ complexInv Y =
      complexInv X := sorry

/-- Degreewise forward naturality is the commutative square between the two model
identifications and the canonical homogeneous comparison. -/
theorem complexHom_f_naturality
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ) :
    (complexHom X).f n ≫
        ((X.chainComparison Y).toChainHom.natRestriction).f n =
      (complexHom Y).f n := sorry

/-- The comparison isomorphism on homology induced by the canonical natural-complex comparison
between two supplied base-change models. -/
@[stacks 09PL "homology comparison of base-change models",
  stacks 09PQ "homology comparison of base-change models"]
noncomputable def comparisonHomologyIso
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ) :
    X.algebra.toChainDGAlgebra.natRestriction.homology n ≅
      Y.algebra.toChainDGAlgebra.natRestriction.homology n :=
  HomologicalComplex.homologyMapIso (comparisonComplexIso X Y) n

/-- The forward model comparison on homology is induced by the restricted canonical chain-DGA
comparison. -/
@[simp]
theorem comparisonHomologyIso_hom
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ) :
    (comparisonHomologyIso X Y n).hom =
      HomologicalComplex.homologyMap
        ((X.chainComparison Y).toChainHom.natRestriction) n := sorry

/-- The inverse model comparison on homology is induced by the reverse canonical chain-DGA
comparison. -/
@[simp]
theorem comparisonHomologyIso_inv
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ) :
    (comparisonHomologyIso X Y n).inv =
      HomologicalComplex.homologyMap
        ((Y.chainComparison X).toChainHom.natRestriction) n := sorry

/-- Homology of the scalar-extension complex is natural as an isomorphism under comparison of
two supplied base-change models. -/
theorem homologyIso_naturality
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ) :
    (homologyIso X n).trans (comparisonHomologyIso X Y n) =
      homologyIso Y n := sorry

/-- The forward homology maps commute with canonical comparison of supplied base-change
models. -/
theorem homologyIso_hom_naturality
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ) :
    (homologyIso X n).hom ≫
        HomologicalComplex.homologyMap
          ((X.chainComparison Y).toChainHom.natRestriction) n =
      (homologyIso Y n).hom := sorry

/-- The inverse homology maps commute with canonical comparison of supplied base-change
models. -/
theorem homologyIso_inv_naturality
    (X Y : DividedPowerChainAlgebra.BaseChange (R' := S) A) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((X.chainComparison Y).toChainHom.natRestriction) n ≫
          (homologyIso Y n).inv =
      (homologyIso X n).inv := sorry

end DividedPowerChainAlgebra.BaseChange.NatRestriction
