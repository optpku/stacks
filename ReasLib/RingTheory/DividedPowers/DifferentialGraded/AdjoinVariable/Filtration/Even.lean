module

public import ReasLib.Algebra.Category.ModuleCat.Filtration.HomologicalComplex
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.NatRestriction
public import ReasLib.CategoryTheory.Filtration.Complex.Convergence
public import ReasLib.CategoryTheory.Filtration.GradedPiece.Comparison
public import ReasLib.CategoryTheory.Filtration.ZeroObject
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.AdjoinVariable.Model.Even

/-!
# The exponent filtration on an even divided-power cell

An even cell has homogeneous coefficient pieces
`A_m T^[0] ⊕ A_{m-d} T^[1] ⊕ ⋯`.  This file filters those pieces by an upper bound
on the divided-monomial exponent.  Since `FilteredObject` uses decreasing integer filtrations,
the stage indexed by `p : ℤ` consists of the terms with exponent `i ≤ -p`.

The construction is made on the natural-degree restriction of the actual chain DGA and is then
extended along `ComplexShape.embeddingDownNat` to a filtered cochain complex.  Thus it is a
genuine input to the project's spectral-sequence and convergence APIs, rather than a separately
postulated spectral sequence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace DividedPowerChainAlgebra.Adjoin.Even.Extension.ExponentFiltration

variable {R : Type u} [CommRing R]
variable {A : DividedPowerChainAlgebra.{u, v} R} {d : ℕ+}
variable {f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}

/-- The coefficient index of the `i`-th divided monomial in total degree `k + i * d`. -/
def coeffIndex (d k i : ℕ) : {j : ℕ // j * d ≤ k + i * d} :=
  ⟨i, Nat.le_add_left (i * d) k⟩

/-- Insert a homogeneous coefficient as the `i`-th divided monomial. -/
def coeffMonomial (A : NonnegGradedAlgebra.{u, v} R) (d k i : ℕ) :
    A.piece k →ₗ[R] NonnegGradedAlgebra.Adjoin.Even.Piece A d (k + i * d) :=
  (DFinsupp.lsingle (coeffIndex d k i)).comp
    (A.pieceCast (Nat.add_sub_cancel_right k (i * d)).symm)

/-- Extract the coefficient of the `i`-th divided monomial in total degree `k + i * d`. -/
def coeffProjection (A : NonnegGradedAlgebra.{u, v} R) (d k i : ℕ) :
    NonnegGradedAlgebra.Adjoin.Even.Piece A d (k + i * d) →ₗ[R] A.piece k :=
  (A.pieceCast (Nat.add_sub_cancel_right k (i * d))).comp
    (DFinsupp.lapply (coeffIndex d k i))

/-- Coefficient extraction is a left inverse to insertion at the same exponent. -/
@[simp]
theorem coeffProjection_coeffMonomial (A : NonnegGradedAlgebra.{u, v} R)
    (d k i : ℕ) (x : A.piece k) :
    coeffProjection A d k i (coeffMonomial A d k i x) = x := sorry

/-- A coefficient vector is supported at exponents at most `-p`. -/
def SupportedUpTo (A : NonnegGradedAlgebra.{u, v} R) (d m : ℕ) (p : ℤ)
    (x : NonnegGradedAlgebra.Adjoin.Even.Piece A d m) : Prop :=
  ∀ i : {i : ℕ // i * d ≤ m}, -p < (i : ℤ) → x i = 0

/-- The zero coefficient vector is supported at every exponent bound. -/
theorem supportedUpTo_zero (A : NonnegGradedAlgebra.{u, v} R) (d m : ℕ) (p : ℤ) :
    SupportedUpTo A d m p 0 := sorry

/-- The sum of two coefficient vectors with the same exponent bound has that bound. -/
theorem SupportedUpTo.add (A : NonnegGradedAlgebra.{u, v} R) (d m : ℕ) (p : ℤ)
    {x y : NonnegGradedAlgebra.Adjoin.Even.Piece A d m}
    (hx : SupportedUpTo A d m p x) (hy : SupportedUpTo A d m p y) :
    SupportedUpTo A d m p (x + y) := sorry

/-- Scalar multiplication does not enlarge divided-monomial support. -/
theorem SupportedUpTo.smul (A : NonnegGradedAlgebra.{u, v} R) (d m : ℕ) (p : ℤ)
    (r : R) {x : NonnegGradedAlgebra.Adjoin.Even.Piece A d m}
    (hx : SupportedUpTo A d m p x) : SupportedUpTo A d m p (r • x) := sorry

/-- The submodule of a homogeneous coefficient piece supported in exponents `i ≤ -p`. -/
def coeffStage (A : NonnegGradedAlgebra.{u, v} R) (d m : ℕ) (p : ℤ) :
    Submodule R (NonnegGradedAlgebra.Adjoin.Even.Piece A d m) where
  carrier := SupportedUpTo A d m p
  zero_mem' := supportedUpTo_zero A d m p
  add_mem' := SupportedUpTo.add A d m p
  smul_mem' := SupportedUpTo.smul A d m p

/-- Membership in a coefficient stage is the explicit upper-support condition. -/
@[simp]
theorem mem_coeffStage_iff (A : NonnegGradedAlgebra.{u, v} R) (d m : ℕ) (p : ℤ)
    (x : NonnegGradedAlgebra.Adjoin.Even.Piece A d m) :
    x ∈ coeffStage A d m p ↔
      ∀ i : {i : ℕ // i * d ≤ m}, -p < (i : ℤ) → x i = 0 := sorry

/-- Increasing the decreasing-filtration index shrinks the allowed exponent support. -/
theorem coeffStage_antitone (A : NonnegGradedAlgebra.{u, v} R) (d m : ℕ) :
    Antitone (coeffStage A d m) := sorry

/-- The natural-degree term of an even cell in its explicit coefficient coordinates. -/
def coords (X : Even.Extension A d f) (m : ℕ) :
    X.algebra.toChainDGAlgebra.natRestriction.X m ≃ₗ[R]
      NonnegGradedAlgebra.Adjoin.Even.Piece
        A.toChainDGAlgebra.nonnegativePart (d : ℕ) m :=
  (X.algebra.toChainDGAlgebra.natRestrictionXIso m).toLinearEquiv.trans
    (X.coefficientEquiv m)

/-- The exponent stage on the actual natural-degree term of an even cell. -/
def stage (X : Even.Extension A d f) (m : ℕ) (p : ℤ) :
    Submodule R (X.algebra.toChainDGAlgebra.natRestriction.X m) :=
  (coeffStage A.toChainDGAlgebra.nonnegativePart (d : ℕ) m p).comap
    (coords X m).toLinearMap

/-- Stage membership is detected in the explicit divided-monomial coordinates. -/
@[simp]
theorem mem_stage_iff (X : Even.Extension A d f) (m : ℕ) (p : ℤ)
    (x : X.algebra.toChainDGAlgebra.natRestriction.X m) :
    x ∈ stage X m p ↔
      ∀ i : {i : ℕ // i * (d : ℕ) ≤ m},
        -p < (i : ℤ) → coords X m x i = 0 := sorry

/-- The exponent stages form a decreasing integer filtration in every chain degree. -/
theorem stage_antitone (X : Even.Extension A d f) (m : ℕ) :
    Antitone (stage X m) := sorry

/-- The differential of an even cell preserves the upper exponent bound. -/
theorem differential_preserves (X : Even.Extension A d f) (m n : ℕ) :
    ModuleCat.SubmoduleFiltration.Preserves
      (X.algebra.toChainDGAlgebra.natRestriction.d m n).hom (stage X m) (stage X n) := sorry

/-- The reusable submodule filtration on the natural-degree chain complex of an even cell. -/
@[stacks 0GZ6 "even-cell exponent filtration"]
def filtration (X : Even.Extension A d f) :
    HomologicalComplex.SubmoduleFiltration X.algebra.toChainDGAlgebra.natRestriction where
  submodule := stage X
  antitone := stage_antitone X
  d_preserves := differential_preserves X

/-- The natural-degree chain complex of an even cell, valued in filtered modules. -/
@[stacks 0GZ6 "natural-degree filtered even-cell complex"]
def filteredNatComplex (X : Even.Extension A d f) :
    ChainComplex (CategoryTheory.FilteredObject (ModuleCat.{v} R)) ℕ :=
  (filtration X).filtered

/-- The exponent-filtered cochain complex obtained by placing chain degree `m` in cochain
degree `-m`. -/
@[stacks 0GZ6 "filtered complex for an even divided-power cell"]
def filteredComplex (X : Even.Extension A d f) :
    CategoryTheory.FilteredComplex (ModuleCat.{v} R) :=
  (filteredNatComplex X).extend ComplexShape.embeddingDownNat

/-- Forgetting the filtration on the natural-degree owner recovers the cell's natural
restriction. -/
@[stacks 0GZ6 "underlying natural-degree complex of the even filtration"]
theorem filteredNatComplex_underlying (X : Even.Extension A d f) :
    CategoryTheory.HomologicalComplex.Filtered.underlying (filteredNatComplex X) =
      X.algebra.toChainDGAlgebra.natRestriction := sorry

/-- Forgetting the filtration after extension recovers the corresponding extension of the
natural-degree chain complex. -/
@[stacks 0GZ6 "underlying cochain complex of the even filtration"]
theorem filteredComplex_underlying (X : Even.Extension A d f) :
    (filteredComplex X).underlying =
      X.algebra.toChainDGAlgebra.natRestriction.extend ComplexShape.embeddingDownNat := sorry

/-- Positive filtration indices give the zero exponent stage. -/
theorem stage_eq_bot_of_pos (X : Even.Extension A d f) (m : ℕ) (p : ℤ) (hp : 0 < p) :
    stage X m p = ⊥ := sorry

/-- In chain degree `m`, every index at most `-m` gives the full exponent stage. -/
theorem stage_eq_top_of_le_neg_degree (X : Even.Extension A d f) (m : ℕ) (p : ℤ)
    (hp : p ≤ -(m : ℤ)) : stage X m p = ⊤ := sorry

/-- Every term of the exponent-filtered cochain complex has a finite filtration. -/
@[stacks 0GZ6 "bounded exponent filtration"]
theorem hasFiniteFiltrations (X : Even.Extension A d f) :
    (filteredComplex X).HasFiniteFiltrations := sorry

/-- A base coefficient times `T^[i]`, regarded as an element of the actual cell. -/
def monomial (X : Even.Extension A d f) (k i : ℕ) :
    A.toChainDGAlgebra.nonnegativePiece k →ₗ[R]
      X.algebra.toChainDGAlgebra.natRestriction.X (k + i * (d : ℕ)) :=
  (coords X (k + i * (d : ℕ))).symm.toLinearMap.comp
    (coeffMonomial A.toChainDGAlgebra.nonnegativePart (d : ℕ) k i)

/-- In coefficient coordinates, `monomial X k i` has exactly one coefficient at exponent `i`. -/
@[simp]
theorem coords_monomial (X : Even.Extension A d f) (k i : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePiece k) :
    coords X (k + i * (d : ℕ)) (monomial X k i x) =
      coeffMonomial A.toChainDGAlgebra.nonnegativePart (d : ℕ) k i x := sorry

/-- The monomial of exponent `i` belongs to filtration stage `-i`. -/
theorem monomial_mem_stage (X : Even.Extension A d f) (k i : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePiece k) :
    monomial X k i x ∈ stage X (k + i * (d : ℕ)) (-(i : ℤ)) := sorry

/-- The next filtration stage kills the coefficient at exponent `i`. -/
theorem coeffProjection_eq_zero_of_mem_next (X : Even.Extension A d f) (k i : ℕ)
    (x : X.algebra.toChainDGAlgebra.natRestriction.X (k + i * (d : ℕ)))
    (hx : x ∈ stage X (k + i * (d : ℕ)) (-(i : ℤ) + 1)) :
    coeffProjection A.toChainDGAlgebra.nonnegativePart (d : ℕ) k i
      (coords X (k + i * (d : ℕ)) x) = 0 := sorry

/-! ## The associated graded piece at one exponent -/

/-- Projection from stage `-i` to the coefficient of `T^[i]`. -/
def stageProjection (X : Even.Extension A d f) (k i : ℕ) :
    stage X (k + i * (d : ℕ)) (-(i : ℤ)) →ₗ[R]
      A.toChainDGAlgebra.nonnegativePiece k :=
  (coeffProjection A.toChainDGAlgebra.nonnegativePart (d : ℕ) k i).comp <|
    (coords X (k + i * (d : ℕ))).toLinearMap.comp
      (stage X (k + i * (d : ℕ)) (-(i : ℤ))).subtype

/-- The monomial inclusion with codomain restricted to stage `-i`. -/
def stageMonomial (X : Even.Extension A d f) (k i : ℕ) :
    A.toChainDGAlgebra.nonnegativePiece k →ₗ[R]
      stage X (k + i * (d : ℕ)) (-(i : ℤ)) :=
  LinearMap.codRestrict (stage X (k + i * (d : ℕ)) (-(i : ℤ)))
    (monomial X k i) (monomial_mem_stage X k i)

/-- Coefficient projection is a left inverse to the restricted monomial inclusion. -/
@[simp]
theorem stageProjection_stageMonomial (X : Even.Extension A d f) (k i : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePiece k) :
    stageProjection X k i (stageMonomial X k i x) = x := sorry

/-- The categorical stage of the exponent filtration is the module carried by its explicit
submodule. -/
def stageIso (X : Even.Extension A d f) (k i : ℕ) :
    ((filtration X).term (k + i * (d : ℕ))).stage (-(i : ℤ)) ≅
      ModuleCat.of R (stage X (k + i * (d : ℕ)) (-(i : ℤ))) :=
  ModuleCat.SubobjectModule.underlyingIso
    (X.algebra.toChainDGAlgebra.natRestriction.X (k + i * (d : ℕ)))
    (stage X (k + i * (d : ℕ)) (-(i : ℤ)))

/-- The categorical projection from stage `-i` to the coefficient module of `T^[i]`. -/
def projection (X : Even.Extension A d f) (k i : ℕ) :
    ((filtration X).term (k + i * (d : ℕ))).stage (-(i : ℤ)) ⟶
      ModuleCat.of R (A.toChainDGAlgebra.nonnegativePiece k) :=
  (stageIso X k i).hom ≫ ModuleCat.ofHom (stageProjection X k i)

/-- The monomial section followed by the quotient projection into the graded piece. -/
def monomialClass (X : Even.Extension A d f) (k i : ℕ) :
    ModuleCat.of R (A.toChainDGAlgebra.nonnegativePiece k) ⟶
      ((filtration X).term (k + i * (d : ℕ))).gradedPiece (-(i : ℤ)) :=
  ModuleCat.ofHom (stageMonomial X k i) ≫ (stageIso X k i).inv ≫
    cokernel.π (((filtration X).term (k + i * (d : ℕ))).succInclusion (-(i : ℤ)))

/-- Projection to the exponent-`i` coefficient annihilates the next filtration stage. -/
theorem succInclusion_projection (X : Even.Extension A d f) (k i : ℕ) :
    ((filtration X).term (k + i * (d : ℕ))).succInclusion (-(i : ℤ)) ≫
      projection X k i = 0 := sorry

/-- The quotient descent from the exponent-`i` graded piece to its base coefficient module. -/
def gradedProjection (X : Even.Extension A d f) (k i : ℕ) :
    ((filtration X).term (k + i * (d : ℕ))).gradedPiece (-(i : ℤ)) ⟶
      ModuleCat.of R (A.toChainDGAlgebra.nonnegativePiece k) :=
  FilteredObject.GradedPiece.desc ((filtration X).term (k + i * (d : ℕ)))
    (-(i : ℤ)) (projection X k i) (succInclusion_projection X k i)

/-- The coefficient descent and monomial class satisfy the two-sided graded-piece comparison
specification. -/
theorem gradedPieceComparison (X : Even.Extension A d f) (k i : ℕ) :
    FilteredObject.GradedPiece.Comparison
      ((filtration X).term (k + i * (d : ℕ))) (-(i : ℤ))
      (projection X k i) (gradedProjection X k i) (monomialClass X k i) := sorry

/-- The exponent-`i` associated graded piece in total degree `k + i * d` is canonically the
degree-`k` piece of the base DGA. -/
@[stacks 0GZ6 "graded piece of the even-cell exponent filtration"]
def gradedPieceIso (X : Even.Extension A d f) (k i : ℕ) :
    ((filtration X).term (k + i * (d : ℕ))).gradedPiece (-(i : ℤ)) ≅
      ModuleCat.of R (A.toChainDGAlgebra.nonnegativePiece k) :=
  (gradedPieceComparison X k i).isoOf

/-- The forward graded-piece isomorphism is the canonical coefficient descent. -/
@[simp]
theorem gradedPieceIso_hom (X : Even.Extension A d f) (k i : ℕ) :
    (gradedPieceIso X k i).hom = gradedProjection X k i := sorry

/-- The inverse graded-piece isomorphism is the monomial class. -/
@[simp]
theorem gradedPieceIso_inv (X : Even.Extension A d f) (k i : ℕ) :
    (gradedPieceIso X k i).inv = monomialClass X k i := sorry

/-- Under the graded-piece identifications, the associated-graded differential is the base
differential with the expected degree shift by `i * d`. -/
theorem gradedDifferential (X : Even.Extension A d f) (k i : ℕ) :
    ((filteredNatComplex X).d ((k + 1) + i * (d : ℕ)) (k + i * (d : ℕ))).gradedPieceMap
        (-(i : ℤ)) ≫
      (gradedPieceIso X k i).hom =
    (gradedPieceIso X (k + 1) i).hom ≫
      ModuleCat.ofHom
        (A.toChainDGAlgebra.nonnegativeDifferential ⟨k + 1, Nat.zero_lt_succ k⟩) := sorry

/-! ## Coefficient formulas for the differential -/

/-- Casting between equal total degrees preserves addition on even-variable coefficient pieces. -/
theorem coeffPieceCast_add (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ) {m n : ℕ}
    (h : m = n) (x y : NonnegGradedAlgebra.Adjoin.Even.Piece A d m) :
    cast (congrArg (NonnegGradedAlgebra.Adjoin.Even.Piece A d) h) (x + y) =
      cast (congrArg (NonnegGradedAlgebra.Adjoin.Even.Piece A d) h) x +
        cast (congrArg (NonnegGradedAlgebra.Adjoin.Even.Piece A d) h) y := sorry

/-- Casting between equal total degrees preserves scalar multiplication on coefficient pieces. -/
theorem coeffPieceCast_smul (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ) {m n : ℕ}
    (h : m = n) (r : R) (x : NonnegGradedAlgebra.Adjoin.Even.Piece A d m) :
    cast (congrArg (NonnegGradedAlgebra.Adjoin.Even.Piece A d) h) (r • x) =
      r • cast (congrArg (NonnegGradedAlgebra.Adjoin.Even.Piece A d) h) x := sorry

/-- Linear transport between equal total degrees of the coefficient presentation. -/
def coeffPieceCast (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ) {m n : ℕ}
    (h : m = n) : NonnegGradedAlgebra.Adjoin.Even.Piece A d m →ₗ[R]
      NonnegGradedAlgebra.Adjoin.Even.Piece A d n where
  toFun x := cast (congrArg (NonnegGradedAlgebra.Adjoin.Even.Piece A d) h) x
  map_add' := coeffPieceCast_add A d h
  map_smul' := coeffPieceCast_smul A d h

/-- The source degree of a same-exponent differential calculation is positive. -/
def sameSourceDegree (d : ℕ+) (k i : ℕ) : ℕ+ :=
  ⟨(k + 1) + i * (d : ℕ), Nat.add_pos_left (Nat.zero_lt_succ k) (i * (d : ℕ))⟩

/-- Removing one from a same-exponent source degree leaves `k + i * d`. -/
theorem sameTargetDegree (d : ℕ+) (k i : ℕ) :
    (((sameSourceDegree d k i : ℕ) - 1 : ℕ)) = k + i * (d : ℕ) := sorry

/-- Projection to exponent `i` after differentiating a coefficient in base degree `k + 1`. -/
def sameProjection (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ+) (k i : ℕ) :
    NonnegGradedAlgebra.Adjoin.Even.Piece A d ((sameSourceDegree d k i : ℕ) - 1) →ₗ[R]
      A.piece k :=
  (coeffProjection A d k i).comp (coeffPieceCast A d (sameTargetDegree d k i))

/-- The source degree of an exponent-lowering differential calculation is positive. -/
def lowerSourceDegree (d : ℕ+) (k i : ℕ) : ℕ+ :=
  ⟨k + (i + 1) * (d : ℕ),
    Nat.add_pos_right k (Nat.mul_pos (Nat.zero_lt_succ i) d.property)⟩

/-- After lowering exponent `i + 1` to `i`, the new base degree is `(d - 1) + k`. -/
theorem lowerTargetDegree (d : ℕ+) (k i : ℕ) :
    (((lowerSourceDegree d k i : ℕ) - 1 : ℕ)) =
      (((d : ℕ) - 1) + k) + i * (d : ℕ) := sorry

/-- Projection to the coefficient at exponent `i` after differentiating exponent `i + 1`. -/
def lowerProjection (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ+) (k i : ℕ) :
    NonnegGradedAlgebra.Adjoin.Even.Piece A d ((lowerSourceDegree d k i : ℕ) - 1) →ₗ[R]
      A.piece (((d : ℕ) - 1) + k) :=
  (coeffProjection A d (((d : ℕ) - 1) + k) i).comp
    (coeffPieceCast A d (lowerTargetDegree d k i))

/-- Left multiplication by the attaching cycle preserves addition. -/
theorem attachingMul_add (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (k : ℕ)
    (x y : A.toChainDGAlgebra.nonnegativePiece k) :
    A.toChainDGAlgebra.nonnegativeMul f (x + y) =
      A.toChainDGAlgebra.nonnegativeMul f x + A.toChainDGAlgebra.nonnegativeMul f y := sorry

/-- Left multiplication by the attaching cycle preserves scalar multiplication. -/
theorem attachingMul_smul (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (k : ℕ)
    (r : R) (x : A.toChainDGAlgebra.nonnegativePiece k) :
    A.toChainDGAlgebra.nonnegativeMul f (r • x) =
      r • A.toChainDGAlgebra.nonnegativeMul f x := sorry

/-- The homogeneous linear map given by left multiplication by the attaching cycle. -/
def attachingMul (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (k : ℕ) :
    A.toChainDGAlgebra.nonnegativePiece k →ₗ[R]
      A.toChainDGAlgebra.nonnegativePiece (((d : ℕ) - 1) + k) where
  toFun x := A.toChainDGAlgebra.nonnegativeMul f x
  map_add' := attachingMul_add A d f k
  map_smul' := attachingMul_smul A d f k

/-- The same-exponent coefficient of the cell differential is the base differential. -/
theorem coeffDifferential_sameExponent (X : Even.Extension A d f) (k i : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePiece (k + 1)) :
    sameProjection A.toChainDGAlgebra.nonnegativePart d k i
        (X.coeffDifferential (sameSourceDegree d k i)
          (coeffMonomial A.toChainDGAlgebra.nonnegativePart (d : ℕ) (k + 1) i x)) =
      A.toChainDGAlgebra.nonnegativeDifferential ⟨k + 1, Nat.zero_lt_succ k⟩ x := sorry

/-- The exponent-lowering coefficient of the cell differential is multiplication by the
attaching cycle.  This is the chain-level formula needed to identify the generic first-page
boundary with `ξ T^[i+1] ↦ [f ξ] T^[i]`; it does not choose or postulate a spectral-sequence
association. -/
@[stacks 0GZ6 "coefficient formula inducing the first differential"]
theorem coeffDifferential_lowerExponent (X : Even.Extension A d f) (k i : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePiece k) :
    lowerProjection A.toChainDGAlgebra.nonnegativePart d k i
        (X.coeffDifferential (lowerSourceDegree d k i)
          (coeffMonomial A.toChainDGAlgebra.nonnegativePart (d : ℕ) k (i + 1) x)) =
      attachingMul A d f k x := sorry

end DividedPowerChainAlgebra.Adjoin.Even.Extension.ExponentFiltration
