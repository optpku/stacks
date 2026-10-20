module

public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Equiv.Fin.Basic
public import ReasLib.NumberTheory.Automorphic.RamifiedCuspForm
public import ReasLib.NumberTheory.Automorphic.UnramifiedHecke

/-!
# Spherical Hecke operators for general linear groups
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory Matrix
open Finset TopologicalSpace
open scoped RestrictedProduct

universe u v

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable (X : SchemeOverField k)
variable [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]

/-- The diagonal matrix `diag(π^{-1}, …, π^{-1}, 1, …, 1)` in `GL (Fin n) K_v`
with `i` copies of `π^{-1}`. -/
def satakeLocalDiag (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    (π : (completion X v)ˣ) : GL (Fin n) (completion X v) where
  val := Matrix.diagonal fun j ↦ if j.val < i then π.inv else 1
  inv := Matrix.diagonal fun j ↦ if j.val < i then π.val else 1
  val_inv := sorry
  inv_val := sorry

/-- Unfolding of `satakeLocalDiag` as the displayed diagonal matrix. -/
theorem satakeLocalDiag_spec (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    (π : (completion X v)ˣ) :
    (satakeLocalDiag X n v i π).val =
      Matrix.diagonal fun j ↦ if j.val < i then π.inv else 1 := sorry

/-- The spherical diagonal element `diag(π^{-1}^i, 1^{n-i})` embedded in
`GL (Fin n) A`. -/
def satakeDiag (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    (π : (completion X v)ˣ) : GL (Fin n) (adeleRing X) :=
  embedLocalGL X n v (satakeLocalDiag X n v i π)

/-- `satakeDiag` is the local embedding of `satakeLocalDiag`. -/
theorem satakeDiag_spec (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    (π : (completion X v)ˣ) :
    satakeDiag X n v i π =
      embedLocalGL X n v (satakeLocalDiag X n v i π) := sorry

/-- The Grassmannian of `i`-planes in `κ(v)^n`, indexing left `GL(O_v)`-cosets
in the spherical double coset of `diag(π^{-1}^i, 1^{n-i})`. -/
structure HeckeCosetIndex (n : ℕ) (v : closedPoints X.left) (i : ℕ) where
  /-- The underlying `i`-plane in `κ(v)^n`. -/
  carrier : Submodule (X.left.residueField v.1)
    (Fin n → X.left.residueField v.1)
  /-- The packaged subspace has finite rank `i`. -/
  finrank_eq : Module.finrank (X.left.residueField v.1) carrier = i

/-- Package an `i`-plane in `κ(v)^n` as a spherical Hecke-coset index. -/
def HeckeCosetIndex.of (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (carrier : Submodule (X.left.residueField v.1)
      (Fin n → X.left.residueField v.1))
    (finrank_eq : Module.finrank (X.left.residueField v.1) carrier = i) :
    HeckeCosetIndex X n v i :=
  ⟨carrier, finrank_eq⟩

/-- The carrier of `HeckeCosetIndex.of` is the given subspace. -/
theorem HeckeCosetIndex.of_carrier (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (carrier : Submodule (X.left.residueField v.1)
      (Fin n → X.left.residueField v.1))
    (finrank_eq : Module.finrank (X.left.residueField v.1) carrier = i) :
    (HeckeCosetIndex.of X n v carrier finrank_eq).carrier = carrier := sorry

/-- The packaged plane has finite rank `i`. -/
theorem HeckeCosetIndex.spec (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) :
    Module.finrank (X.left.residueField v.1) W.carrier = i := sorry

/-- Submodules of a finite vector space over a finite residue field are finite. -/
instance instFinite_submodule (n : ℕ) (v : closedPoints X.left)
    [Finite (X.left.residueField v.1)] :
    Finite
      (Submodule (X.left.residueField v.1)
        (Fin n → X.left.residueField v.1)) :=
  Finite.of_injective
    (SetLike.coe :
      Submodule (X.left.residueField v.1) (Fin n → X.left.residueField v.1) →
        Set (Fin n → X.left.residueField v.1))
    SetLike.coe_injective

/-- The finite set of all subspaces of the prescribed dimension. -/
def HeckeCosetIndex.elems (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    [Finite (X.left.residueField v.1)] : Finset (HeckeCosetIndex X n v i) :=
  open Classical in
  (let indexType := {W : Submodule (X.left.residueField v.1)
      (Fin n → X.left.residueField v.1) //
      Module.finrank (X.left.residueField v.1) W = i}
   (Fintype.ofFinite indexType).elems).image
    (fun W ↦ HeckeCosetIndex.of X n v W.1 W.2)

/-- Every subspace of the prescribed dimension belongs to the enumeration. -/
theorem HeckeCosetIndex.mem_elems (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    [Finite (X.left.residueField v.1)] (W : HeckeCosetIndex X n v i) :
    W ∈ HeckeCosetIndex.elems X n v i := sorry

/-- Complementary subspace to an `i`-plane in `κ(v)^n`. -/
def grassmannianComplement (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) :
    Submodule (X.left.residueField v.1) (Fin n → X.left.residueField v.1) :=
  LinearMap.ker W.carrier.subtype.leftInverse

/-- `grassmannianComplement` is complementary to `W`. -/
theorem grassmannianComplement_isCompl (n : ℕ) (v : closedPoints X.left)
    {i : ℕ} (W : HeckeCosetIndex X n v i) :
    IsCompl W.carrier (grassmannianComplement X n v W) := sorry

/-- A basis of the `i`-plane `W`. -/
def grassmannianWBasis (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) :
    Module.Basis (Fin i) (X.left.residueField v.1) W.carrier :=
  Module.finBasisOfFinrankEq (X.left.residueField v.1) W.carrier W.finrank_eq

/-- A basis of the complementary subspace to `W`. -/
def grassmannianComplBasis (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) :
    Module.Basis (Fin (n - i)) (X.left.residueField v.1)
      (grassmannianComplement X n v W) :=
  let hsum :=
    Submodule.finrank_add_eq_of_isCompl
      (LinearMap.isCompl_of_proj
        (LinearMap.leftInverse_apply_of_inj W.carrier.ker_subtype))
  Module.finBasisOfFinrankEq (X.left.residueField v.1)
    (grassmannianComplement X n v W)
    (Nat.eq_sub_of_add_eq
      ((Nat.add_comm
          (Module.finrank (X.left.residueField v.1)
            (grassmannianComplement X n v W))
          i).trans
        (((Eq.symm
              (congrArg
                (fun m : ℕ ↦
                  Nat.add m
                    (Module.finrank (X.left.residueField v.1)
                      (grassmannianComplement X n v W)))
                W.finrank_eq)).trans hsum).trans
          (Module.finrank_fin_fun (X.left.residueField v.1)))))

/-- A basis of `κ(v)^n` whose first `i` vectors span `W` and whose remaining
vectors span a complementary subspace. -/
def grassmannianFrameBasis (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) :
    Module.Basis (Fin i ⊕ Fin (n - i)) (X.left.residueField v.1)
      (Fin n → X.left.residueField v.1) :=
  ((grassmannianWBasis X n v W).prod (grassmannianComplBasis X n v W)).map
    (Submodule.prodEquivOfIsCompl W.carrier (grassmannianComplement X n v W)
      (LinearMap.isCompl_of_proj
        (LinearMap.leftInverse_apply_of_inj W.carrier.ker_subtype)))

/-- Residue-level frame in `GL (Fin n, κ(v))` whose first `i` columns are a
basis of `W` and whose remaining columns complete it to a basis of `κ(v)^n`. -/
def grassmannianResidueMatrix (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) :
    Matrix (Fin n) (Fin n) (X.left.residueField v.1) :=
  fun row col ↦
    if h : i ≤ n then
      ((grassmannianFrameBasis X n v W).reindex
          (finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))) col :
        Fin n → X.left.residueField v.1) row
    else if row = col then 1 else 0

/-- The residue-level general linear frame of an `i`-plane, with inverse the
adjugate scaled by the inverse determinant. -/
def grassmannianResidueGL (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) :
    GL (Fin n) (X.left.residueField v.1) where
  val := grassmannianResidueMatrix X n v W
  inv :=
    (grassmannianResidueMatrix X n v W).det⁻¹ •
      (grassmannianResidueMatrix X n v W).adjugate
  val_inv := sorry
  inv_val := sorry

/-- The residue determinant of a Grassmannian frame is a unit. -/
theorem grassmannianResidueGL_isUnit (n : ℕ) (v : closedPoints X.left)
    {i : ℕ} (W : HeckeCosetIndex X n v i) :
    IsUnit (grassmannianResidueMatrix X n v W).det := sorry

/-- Lift a residue matrix to a matrix over `O_v`. -/
def liftResidueMatrix (n : ℕ) (v : closedPoints X.left)
    (m : Matrix (Fin n) (Fin n) (X.left.residueField v.1)) :
    Matrix (Fin n) (Fin n) (completionIntegers X v) :=
  fun a b ↦ residueSectionIntegers X v (m a b)

/-- The `O_v`-lift of a residue matrix coerces to `residueRep` entrywise. -/
theorem liftResidueMatrix_apply (n : ℕ) (v : closedPoints X.left)
    (m : Matrix (Fin n) (Fin n) (X.left.residueField v.1)) (a b : Fin n) :
    (liftResidueMatrix X n v m a b : completion X v) =
      residueRep X v (m a b) := sorry

/-- The determinant of the lifted frame is a unit of `O_v`, since its reduction
is the determinant of a basis matrix over `κ(v)`. -/
theorem grassmannianLocalDet_isUnit (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) :
    IsUnit (liftResidueMatrix X n v (grassmannianResidueGL X n v W).val).det := sorry

/-- The integral lift of a Grassmannian frame. Its inverse is computed over
`O_v` itself as the adjugate times the inverse of the unit determinant. -/
def grassmannianLocalGL (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) :
    GL (Fin n) (completionIntegers X v) where
  val := liftResidueMatrix X n v (grassmannianResidueGL X n v W).val
  inv :=
    Ring.inverse (liftResidueMatrix X n v (grassmannianResidueGL X n v W).val).det •
      (liftResidueMatrix X n v (grassmannianResidueGL X n v W).val).adjugate
  val_inv := sorry
  inv_val := sorry

/-- The image of `grassmannianLocalGL` in `GL (Fin n) K_v`. -/
def grassmannianCompletionGL (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) : GL (Fin n) (completion X v) :=
  GeneralLinearGroup.map (ValuationSubring.subtype (completionIntegers X v))
    (grassmannianLocalGL X n v W)

/-- `grassmannianCompletionGL` is `GeneralLinearGroup.map` of the integral
frame along `O_v → K_v`. -/
theorem grassmannianCompletionGL_spec (n : ℕ) (v : closedPoints X.left)
    {i : ℕ} (W : HeckeCosetIndex X n v i) :
    grassmannianCompletionGL X n v W =
      GeneralLinearGroup.map
        (ValuationSubring.subtype (completionIntegers X v))
        (grassmannianLocalGL X n v W) := sorry

/-- From a column frame `g`, form `D * gᵀ`, so the first `i` rows before
scaling span the plane carried by the first `i` columns of `g`. The written
inverse is `(g⁻¹)ᵀ * D⁻¹`. This orientation parametrizes left integral cosets. -/
def heckeLeftRepresentative {R : Type u} [CommRing R] (n i : ℕ)
    (π : Rˣ) (g : GL (Fin n) R) : GL (Fin n) R where
  val := (Matrix.diagonal fun j : Fin n ↦ if j.val < i then π.inv else 1) * g.val.transpose
  inv := g.inv.transpose * (Matrix.diagonal fun j : Fin n ↦ if j.val < i then π.val else 1)
  val_inv := sorry
  inv_val := sorry

/-- The local left-coset representative attached to `W`. Transposing the lifted
column frame makes its first `i` rows span `W`; left multiplication by the
diagonal scales exactly these rows. In degree `n`, use the scalar itself. -/
def heckeLocalCosetRep (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    (W : HeckeCosetIndex X n v i) (π : (completion X v)ˣ) :
    GL (Fin n) (completion X v) :=
  if i = n then satakeLocalDiag X n v i π
  else heckeLeftRepresentative n i π (grassmannianCompletionGL X n v W)

/-- Equality of left `GL(O_v)`-cosets of two local general-linear matrices. -/
def SameLeftHeckeCoset (n : ℕ) (v : closedPoints X.left)
    (r s : GL (Fin n) (completion X v)) : Prop :=
  ∃ a : GL (Fin n) (completionIntegers X v),
    GeneralLinearGroup.map (ValuationSubring.subtype (completionIntegers X v)) a * r = s

/-- Distinct Grassmannian planes give distinct left integral cosets. The
plane is recovered as the reduction modulo `π` of the scaled row lattice. -/
theorem heckeLocalCosetRep_sameLeft_iff (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    (W W' : HeckeCosetIndex X n v i) (π : (completion X v)ˣ)
    (hπ : IsUniformizer X v π.val) :
    SameLeftHeckeCoset X n v (heckeLocalCosetRep X n v i W π)
      (heckeLocalCosetRep X n v i W' π) ↔ W = W' := sorry

/-- The Grassmannian section covers the spherical double coset exactly once
modulo left integral multiplication. -/
theorem heckeLocalCosetRep_complete (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    (hi : i ≤ n) (π : (completion X v)ˣ) (hπ : IsUniformizer X v π.val)
    (a b : GL (Fin n) (completionIntegers X v)) :
    ∃! W : HeckeCosetIndex X n v i,
      SameLeftHeckeCoset X n v (heckeLocalCosetRep X n v i W π)
        (GeneralLinearGroup.map (ValuationSubring.subtype (completionIntegers X v)) a *
          satakeLocalDiag X n v i π *
          GeneralLinearGroup.map (ValuationSubring.subtype (completionIntegers X v)) b) :=
  sorry

/-- The degree-`n` representative is the scalar inverse uniformizer. -/
theorem heckeLocalCosetRep_last (n : ℕ) (v : closedPoints X.left)
    (W : HeckeCosetIndex X n v n) (π : (completion X v)ˣ) :
    heckeLocalCosetRep X n v n W π = GeneralLinearGroup.scalar (Fin n) π⁻¹ := sorry

/-- The line at infinity, spanned by `(1, 0)`, in the rank-two Grassmannian. -/
def heckeLineInfinity (v : closedPoints X.left) : HeckeCosetIndex X 2 v 1 :=
  HeckeCosetIndex.of X 2 v
    (Submodule.span (X.left.residueField v.1) {![1, 0]}) sorry

/-- The affine line spanned by `(-a, 1)`, corresponding to the off-diagonal
rank-two Hecke representative with residue parameter `a`. -/
def heckeLineAffine (v : closedPoints X.left) (a : X.left.residueField v.1) :
    HeckeCosetIndex X 2 v 1 :=
  HeckeCosetIndex.of X 2 v
    (Submodule.span (X.left.residueField v.1) {![-a, 1]}) sorry

/-- Infinity and the affine residue parameters enumerate the rank-two
Grassmannian without repetition. -/
theorem heckeLines_bijective (v : closedPoints X.left) :
    Function.Bijective (fun a : Option (X.left.residueField v.1) ↦
      a.elim (heckeLineInfinity X v) (heckeLineAffine X v)) := sorry

/-- A left `GL(O_v)`-coset representative in the spherical double coset,
obtained from the row-oriented Grassmannian section. -/
def heckeCosetRep (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    (W : HeckeCosetIndex X n v i) (π : (completion X v)ˣ) :
    GL (Fin n) (adeleRing X) :=
  embedLocalGL X n v (heckeLocalCosetRep X n v i W π)

/-- `heckeCosetRep` embeds the local left-coset representative. -/
theorem heckeCosetRep_spec (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    (W : HeckeCosetIndex X n v i) (π : (completion X v)ˣ) :
    heckeCosetRep X n v i W π =
      embedLocalGL X n v (heckeLocalCosetRep X n v i W π) :=
  sorry

/-- The underlying function of the spherical Hecke operator `T_{v,i}`. -/
def heckeTGL_toFun [Finite k] (n : ℕ) (U : X.left.Opens)
    (v : closedPoints (restrictOpen X U).left) (i : ℕ) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ) (x : GL (Fin n) (adeleRing X)) : Λ :=
  ∑ W ∈ HeckeCosetIndex.elems X n (closedPointEmbed X U v) i,
    φ.toFun
      (heckeCosetRep X n (closedPointEmbed X U v) i W
          (uniformizer X (closedPointEmbed X U v)) *
        x)

/-- The spherical Hecke operator `T_{v,i}` associated with the double coset
`GL(O_v) diag(π^{-1}^i, 1^{n-i}) GL(O_v)`. -/
def heckeTGL [Finite k] (n : ℕ) (U : X.left.Opens)
    (v : closedPoints (restrictOpen X U).left) (i : ℕ) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ) : CuspFormGL X n U Λ :=
  CuspFormGL.of (heckeTGL_toFun X n U v i φ) sorry sorry φ.level sorry sorry

/-- `heckeTGL` acts by the displayed sum of left translations over invertible
Grassmannian-frame representatives. -/
theorem heckeTGL_apply [Finite k] (n : ℕ) (U : X.left.Opens)
    (v : closedPoints (restrictOpen X U).left) (i : ℕ) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ) (x : GL (Fin n) (adeleRing X)) :
    (heckeTGL X n U v i φ).toFun x = heckeTGL_toFun X n U v i φ x := sorry

/-- The top-degree Hecke operator is a single translation by the scalar
inverse uniformizer, since the full Grassmannian has one point. -/
theorem heckeTGL_last_apply [Finite k] (n : ℕ) (U : X.left.Opens)
    (v : closedPoints (restrictOpen X U).left) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ) (x : GL (Fin n) (adeleRing X)) :
    (heckeTGL X n U v n φ).toFun x =
      φ.toFun (embedLocalGL X n (closedPointEmbed X U v)
        (GeneralLinearGroup.scalar (Fin n)
          (uniformizer X (closedPointEmbed X U v))⁻¹) * x) := sorry

/-- `T_{v,i}(φ)(x)` is the sum of `φ(γ x)` over left `GL(O_v)`-coset
representatives `γ` in the spherical double coset of `satakeLocalDiag`, for
every uniformizer. -/
theorem heckeTGL_spec [Finite k] (n : ℕ) (U : X.left.Opens)
    (v : closedPoints (restrictOpen X U).left) (i : ℕ) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ) (π : (completion X (closedPointEmbed X U v))ˣ)
    (hπ : IsUniformizer X (closedPointEmbed X U v) π.val)
    (x : GL (Fin n) (adeleRing X)) :
    (heckeTGL X n U v i φ).toFun x =
      ∑ W ∈ HeckeCosetIndex.elems X n (closedPointEmbed X U v) i,
        φ.toFun (heckeCosetRep X n (closedPointEmbed X U v) i W π * x) :=
  sorry

/-- The operator `T_{v,i}` is independent of the choice of uniformizer. -/
theorem heckeTGL_independent [Finite k] (n : ℕ) (U : X.left.Opens)
    (v : closedPoints (restrictOpen X U).left) (i : ℕ) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ)
    (π π' : (completion X (closedPointEmbed X U v))ˣ)
    (hπ : IsUniformizer X (closedPointEmbed X U v) π.val)
    (hπ' : IsUniformizer X (closedPointEmbed X U v) π'.val)
    (x : GL (Fin n) (adeleRing X)) :
    ∑ W ∈ HeckeCosetIndex.elems X n (closedPointEmbed X U v) i,
          φ.toFun (heckeCosetRep X n (closedPointEmbed X U v) i W π * x) =
      ∑ W ∈ HeckeCosetIndex.elems X n (closedPointEmbed X U v) i,
        φ.toFun (heckeCosetRep X n (closedPointEmbed X U v) i W π' * x) :=
  sorry

/-- The line at infinity gives the left integral coset of `heckeTDiag`.
The change of representative is integral, so left-invariant forms have the
same translate. -/
theorem heckeCosetRep_infinity (v : closedPoints X.left)
    (π : (completion X v)ˣ) (hπ : IsUniformizer X v π.val) :
    ∃ a : GL (Fin 2) (completionIntegers X v),
      localIntegerGL X 2 v a * heckeCosetRep X 2 v 1 (heckeLineInfinity X v) π =
        heckeTDiag X v π := sorry

/-- The affine line `(-a, 1)` gives the left integral coset of `heckeTOff a`.
Together with infinity these are exactly the `q_v + 1` rank-two left cosets. -/
theorem heckeCosetRep_affine (v : closedPoints X.left)
    (π : (completion X v)ˣ) (hπ : IsUniformizer X v π.val)
    (a : X.left.residueField v.1) :
    ∃ b : GL (Fin 2) (completionIntegers X v),
      localIntegerGL X 2 v b * heckeCosetRep X 2 v 1 (heckeLineAffine X v a) π =
        heckeTOff X v π (residueRep X v a) := sorry

/-- For `n = 2` and `U = ⊤`, the spherical operator `T_{v,1}` agrees with
`heckeT`. -/
theorem heckeTGL_heckeT {Λ : Type u} [CommRing Λ] [Fintype k]
    [Invertible (ringChar k : Λ)] (φ : UnramifiedCuspForm X Λ)
    (v : closedPoints (restrictOpen X ⊤).left) :
    (heckeTGL X 2 ⊤ v 1 φ.toCuspFormGL).toFun =
      (heckeT X (closedPointEmbed X ⊤ v) φ).toFun := sorry

/-- For `n = 2` and `U = ⊤`, the spherical operator `T_{v,2}` agrees with
`heckeU`. -/
theorem heckeTGL_heckeU {Λ : Type u} [CommRing Λ] [Fintype k]
    [Invertible (ringChar k : Λ)] (φ : UnramifiedCuspForm X Λ)
    (v : closedPoints (restrictOpen X ⊤).left) :
    (heckeTGL X 2 ⊤ v 2 φ.toCuspFormGL).toFun =
      (heckeU X (closedPointEmbed X ⊤ v) φ).toFun := sorry


end AlgebraicGeometry.SchemeOverField
