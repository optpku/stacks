module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Semilinear
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.ChainAlgebra

/-!
# Semilinear morphisms of divided-power chain DGAs

This file lifts the reusable semilinear morphism API for chain DGAs to divided-power chain
DGAs.  The maps on the even and positive-even direct sums are explicit semilinear maps, so
downstream constructions can use either the bundled divided-power identity or its homogeneous
`gammaPiece` form without rebuilding direct-sum infrastructure.
-/

@[expose] public section

noncomputable section

open scoped DirectSum

universe uR uS uT uA uB uC

namespace DividedPowerChainAlgebra

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [CommRing R] [CommRing S] [CommRing T]
variable {A : DividedPowerChainAlgebra.{uR, uA} R}
variable {B : DividedPowerChainAlgebra.{uS, uB} S}
variable {C : DividedPowerChainAlgebra.{uT, uC} T}
variable {sigma : R →+* S} {tau : S →+* T}

namespace Semilinear

/-- The componentwise additive map on even direct sums induced by a semilinear chain-DGA
morphism. -/
def evenAddMap
    (f : ChainDGAlgebra.SemilinearHom sigma A.toChainDGAlgebra B.toChainDGAlgebra) :
    A.toChainDGAlgebra.nonnegativePart.evenPart →+
      B.toChainDGAlgebra.nonnegativePart.evenPart :=
  DirectSum.map fun d ↦
    (f.map (((2 * d : ℕ) : ℤ))).toAddMonoidHom

/-- The componentwise even direct-sum map carries source scalars through the scalar map. -/
theorem evenAddMap_smul
    (f : ChainDGAlgebra.SemilinearHom sigma A.toChainDGAlgebra B.toChainDGAlgebra)
    (r : R) (x : A.toChainDGAlgebra.nonnegativePart.evenPart) :
    evenAddMap f (r • x) = sigma r • evenAddMap f x := sorry

/-- The semilinear map on the full even direct sum induced degreewise by a semilinear
chain-DGA morphism. -/
def evenMap
    (f : ChainDGAlgebra.SemilinearHom sigma A.toChainDGAlgebra B.toChainDGAlgebra) :
    A.toChainDGAlgebra.nonnegativePart.evenPart →ₛₗ[sigma]
      B.toChainDGAlgebra.nonnegativePart.evenPart where
  toFun := evenAddMap f
  map_add' := (evenAddMap f).map_add
  map_smul' := evenAddMap_smul f

/-- The componentwise additive map on positive-even direct sums induced by a semilinear
chain-DGA morphism. -/
def evenPositiveAddMap
    (f : ChainDGAlgebra.SemilinearHom sigma A.toChainDGAlgebra B.toChainDGAlgebra) :
    A.toChainDGAlgebra.nonnegativePart.evenPositivePart →+
      B.toChainDGAlgebra.nonnegativePart.evenPositivePart :=
  DirectSum.map fun d ↦
    (f.map (((2 * (d + 1) : ℕ) : ℤ))).toAddMonoidHom

/-- The componentwise positive-even direct-sum map carries source scalars through the scalar
map. -/
theorem evenPositiveAddMap_smul
    (f : ChainDGAlgebra.SemilinearHom sigma A.toChainDGAlgebra B.toChainDGAlgebra)
    (r : R) (x : A.toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    evenPositiveAddMap f (r • x) =
      sigma r • evenPositiveAddMap f x := sorry

/-- The semilinear map on the positive-even direct sum induced degreewise by a semilinear
chain-DGA morphism. -/
def evenPositiveMap
    (f : ChainDGAlgebra.SemilinearHom sigma A.toChainDGAlgebra B.toChainDGAlgebra) :
    A.toChainDGAlgebra.nonnegativePart.evenPositivePart →ₛₗ[sigma]
      B.toChainDGAlgebra.nonnegativePart.evenPositivePart where
  toFun := evenPositiveAddMap f
  map_add' := (evenPositiveAddMap f).map_add
  map_smul' := evenPositiveAddMap_smul f

end Semilinear

/-- A semilinear homomorphism of divided-power chain DGAs preserves the chain-DGA structure
and the divided-power operations on the positive-even direct sum. -/
@[stacks 09PQ "semilinear morphism of divided-power chain differential graded algebras"]
structure SemilinearHom (sigma : R →+* S) (A : DividedPowerChainAlgebra.{uR, uA} R)
    (B : DividedPowerChainAlgebra.{uS, uB} S) where
  /-- The underlying semilinear chain-DGA homomorphism. -/
  toChainHom :
    ChainDGAlgebra.SemilinearHom sigma A.toChainDGAlgebra B.toChainDGAlgebra
  /-- The total divided-power operations commute with the induced maps on the even and
  positive-even direct sums. -/
  map_gamma (n : ℕ) (x : A.toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    Semilinear.evenMap toChainHom (A.gamma n x) =
      B.gamma n (Semilinear.evenPositiveMap toChainHom x)

namespace SemilinearHom

variable {sigma : R →+* S} {tau : S →+* T}
variable {A : DividedPowerChainAlgebra.{uR, uA} R}
variable {B : DividedPowerChainAlgebra.{uS, uB} S}
variable {C : DividedPowerChainAlgebra.{uT, uC} T}

/-- A semilinear divided-power chain-DGA homomorphism acts degreewise on homogeneous
elements. -/
instance instCoeFun : CoeFun (SemilinearHom sigma A B)
    (fun _ ↦ ∀ n : ℤ, A.toChainDGAlgebra.X n → B.toChainDGAlgebra.X n) where
  coe f := f.toChainHom

/-- Degreewise evaluation is evaluation of the underlying semilinear chain-DGA map. -/
@[simp]
theorem coe_apply (f : SemilinearHom sigma A B) (n : ℤ)
    (x : A.toChainDGAlgebra.X n) :
    f n x = f.toChainHom n x := sorry

/-- A semilinear divided-power morphism preserves addition in every homogeneous degree. -/
@[simp]
theorem map_add (f : SemilinearHom sigma A B) (n : ℤ)
    (x y : A.toChainDGAlgebra.X n) :
    f n (x + y) = f n x + f n y := sorry

/-- A semilinear divided-power morphism carries source scalars through its scalar map. -/
@[simp]
theorem map_smul (f : SemilinearHom sigma A B) (n : ℤ) (r : R)
    (x : A.toChainDGAlgebra.X n) :
    f n (r • x) = sigma r • f n x := sorry

/-- The semilinear map on the homogeneous even piece indexed by `d`. -/
def evenPieceMap (f : SemilinearHom sigma A B) (d : ℕ) :
    A.toChainDGAlgebra.nonnegativePart.piece (2 * d) →ₛₗ[sigma]
      B.toChainDGAlgebra.nonnegativePart.piece (2 * d) :=
  f.toChainHom.map (((2 * d : ℕ) : ℤ))

/-- The semilinear map on the homogeneous positive-even piece indexed by `d`. -/
def evenPositivePieceMap (f : SemilinearHom sigma A B) (d : ℕ) :
    A.toChainDGAlgebra.nonnegativePart.piece (2 * (d + 1)) →ₛₗ[sigma]
      B.toChainDGAlgebra.nonnegativePart.piece (2 * (d + 1)) :=
  f.toChainHom.map (((2 * (d + 1) : ℕ) : ℤ))

/-- The induced semilinear map on the full even direct sum. -/
def evenMap (f : SemilinearHom sigma A B) :
    A.toChainDGAlgebra.nonnegativePart.evenPart →ₛₗ[sigma]
      B.toChainDGAlgebra.nonnegativePart.evenPart :=
  Semilinear.evenMap f.toChainHom

/-- The induced semilinear map on the positive-even direct sum. -/
def evenPositiveMap (f : SemilinearHom sigma A B) :
    A.toChainDGAlgebra.nonnegativePart.evenPositivePart →ₛₗ[sigma]
      B.toChainDGAlgebra.nonnegativePart.evenPositivePart :=
  Semilinear.evenPositiveMap f.toChainHom

/-- Evaluation of the homogeneous even-piece map is degreewise evaluation of the semilinear
divided-power morphism. -/
@[simp]
theorem evenPieceMap_apply (f : SemilinearHom sigma A B) (d : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePart.piece (2 * d)) :
    f.evenPieceMap d x = f (((2 * d : ℕ) : ℤ)) x := sorry

/-- Evaluation of the homogeneous positive-even-piece map is degreewise evaluation of the
semilinear divided-power morphism. -/
@[simp]
theorem evenPositivePieceMap_apply (f : SemilinearHom sigma A B) (d : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePart.piece (2 * (d + 1))) :
    f.evenPositivePieceMap d x = f (((2 * (d + 1) : ℕ) : ℤ)) x := sorry

/-- The even direct-sum map agrees with the homogeneous even maps. -/
@[simp]
theorem evenMap_evenHom (f : SemilinearHom sigma A B) (d : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePart.piece (2 * d)) :
    f.evenMap (A.toChainDGAlgebra.nonnegativePart.evenHom d x) =
      B.toChainDGAlgebra.nonnegativePart.evenHom d (f.evenPieceMap d x) := sorry

/-- The positive-even direct-sum map agrees with the homogeneous positive-even maps. -/
@[simp]
theorem evenPositiveMap_evenPositiveHom (f : SemilinearHom sigma A B) (d : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePart.piece (2 * (d + 1))) :
    f.evenPositiveMap
        (A.toChainDGAlgebra.nonnegativePart.evenPositiveHom d x) =
      B.toChainDGAlgebra.nonnegativePart.evenPositiveHom d
        (f.evenPositivePieceMap d x) := sorry

/-- A semilinear divided-power morphism commutes with the total divided-power operations. -/
@[simp]
theorem map_gamma_apply (f : SemilinearHom sigma A B) (n : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    f.evenMap (A.gamma n x) = B.gamma n (f.evenPositiveMap x) := sorry

/-- A semilinear divided-power morphism commutes with divided powers on every homogeneous
positive-even piece. -/
@[simp]
theorem map_gammaPiece (f : SemilinearHom sigma A B) (n d : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePart.piece (2 * (d + 1))) :
    f.evenPieceMap (n * (d + 1)) (A.gamma.gammaPiece n d x) =
      B.gamma.gammaPiece n d (f.evenPositivePieceMap d x) := sorry

/-- A semilinear divided-power morphism commutes with the differential. -/
@[simp]
theorem map_d (f : SemilinearHom sigma A B) (n : ℤ)
    (x : A.toChainDGAlgebra.X n) :
    f (n - 1) (A.toChainDGAlgebra.d n x) =
      B.toChainDGAlgebra.d n (f n x) := sorry

/-- A semilinear divided-power morphism preserves the homogeneous unit. -/
@[simp]
theorem map_one (f : SemilinearHom sigma A B) :
    f 0 A.toChainDGAlgebra.one = B.toChainDGAlgebra.one := sorry

/-- A semilinear divided-power morphism preserves homogeneous multiplication. -/
@[simp]
theorem map_mul (f : SemilinearHom sigma A B) (n m : ℤ)
    (x : A.toChainDGAlgebra.X n) (y : A.toChainDGAlgebra.X m) :
    f (n + m) (A.toChainDGAlgebra.mul n m x y) =
      B.toChainDGAlgebra.mul n m (f n x) (f m y) := sorry

/-- The identity semilinear chain-DGA map preserves the divided-power operations. -/
theorem id_map_gamma (A : DividedPowerChainAlgebra.{uR, uA} R) (n : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    Semilinear.evenMap (ChainDGAlgebra.SemilinearHom.id A.toChainDGAlgebra)
        (A.gamma n x) =
      A.gamma n
        (Semilinear.evenPositiveMap
          (ChainDGAlgebra.SemilinearHom.id A.toChainDGAlgebra) x) := sorry

/-- The identity semilinear homomorphism of a divided-power chain DGA. -/
def id (A : DividedPowerChainAlgebra.{uR, uA} R) :
    SemilinearHom (RingHom.id R) A A where
  toChainHom := ChainDGAlgebra.SemilinearHom.id A.toChainDGAlgebra
  map_gamma := id_map_gamma A

/-- The identity semilinear divided-power morphism acts pointwise as the identity. -/
@[simp]
theorem id_apply (A : DividedPowerChainAlgebra.{uR, uA} R) (n : ℤ)
    (x : A.toChainDGAlgebra.X n) : id A n x = x := sorry

/-- The identity semilinear divided-power morphism acts identically on the even direct sum. -/
@[simp]
theorem id_evenMap_apply (A : DividedPowerChainAlgebra.{uR, uA} R)
    (x : A.toChainDGAlgebra.nonnegativePart.evenPart) :
    (id A).evenMap x = x := sorry

/-- The identity semilinear divided-power morphism acts identically on the positive-even direct
sum. -/
@[simp]
theorem id_evenPositiveMap_apply (A : DividedPowerChainAlgebra.{uR, uA} R)
    (x : A.toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    (id A).evenPositiveMap x = x := sorry

/-- A composite of semilinear divided-power chain-DGA maps preserves divided powers. -/
theorem comp_map_gamma (g : SemilinearHom tau B C) (f : SemilinearHom sigma A B)
    (n : ℕ) (x : A.toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    Semilinear.evenMap
        (ChainDGAlgebra.SemilinearHom.comp g.toChainHom f.toChainHom)
        (A.gamma n x) =
      C.gamma n
        (Semilinear.evenPositiveMap
          (ChainDGAlgebra.SemilinearHom.comp g.toChainHom f.toChainHom) x) := sorry

/-- Composition of semilinear divided-power chain-DGA homomorphisms. -/
def comp (g : SemilinearHom tau B C) (f : SemilinearHom sigma A B) :
    SemilinearHom (tau.comp sigma) A C where
  toChainHom := ChainDGAlgebra.SemilinearHom.comp g.toChainHom f.toChainHom
  map_gamma := comp_map_gamma g f

/-- Composition of semilinear divided-power morphisms acts pointwise. -/
@[simp]
theorem comp_apply (g : SemilinearHom tau B C) (f : SemilinearHom sigma A B)
    (n : ℤ) (x : A.toChainDGAlgebra.X n) :
    comp g f n x = g n (f n x) := sorry

/-- Composition of semilinear divided-power morphisms acts by composition on the even direct
sum. -/
@[simp]
theorem comp_evenMap_apply (g : SemilinearHom tau B C) (f : SemilinearHom sigma A B)
    (x : A.toChainDGAlgebra.nonnegativePart.evenPart) :
    (comp g f).evenMap x = g.evenMap (f.evenMap x) := sorry

/-- Composition of semilinear divided-power morphisms acts by composition on the positive-even
direct sum. -/
@[simp]
theorem comp_evenPositiveMap_apply
    (g : SemilinearHom tau B C) (f : SemilinearHom sigma A B)
    (x : A.toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    (comp g f).evenPositiveMap x = g.evenPositiveMap (f.evenPositiveMap x) := sorry

/-- Semilinear divided-power morphisms are determined by their underlying semilinear
chain-DGA maps. -/
theorem ext_toChainHom {f g : SemilinearHom sigma A B}
    (h : f.toChainHom = g.toChainHom) : f = g := sorry

/-- Semilinear divided-power morphisms are determined degreewise. -/
@[ext]
theorem ext {f g : SemilinearHom sigma A B}
    (h : ∀ (n : ℤ) (x : A.toChainDGAlgebra.X n), f n x = g n x) :
    f = g := sorry

/-- A semilinear divided-power morphism is surjective when its homogeneous maps are all
surjective. -/
def Surjective (f : SemilinearHom sigma A B) : Prop :=
  f.toChainHom.Surjective

/-- A semilinear divided-power morphism is injective when its homogeneous maps are all
injective. -/
def Injective (f : SemilinearHom sigma A B) : Prop :=
  f.toChainHom.Injective

/-- A semilinear divided-power morphism is bijective when it is both injective and
surjective degreewise. -/
def Bijective (f : SemilinearHom sigma A B) : Prop :=
  f.Injective ∧ f.Surjective

/-- The identity semilinear divided-power morphism is degreewise surjective. -/
theorem id_surjective (A : DividedPowerChainAlgebra.{uR, uA} R) :
    (id A).Surjective := sorry

/-- The identity semilinear divided-power morphism is degreewise injective. -/
theorem id_injective (A : DividedPowerChainAlgebra.{uR, uA} R) :
    (id A).Injective := sorry

/-- The identity semilinear divided-power morphism is degreewise bijective. -/
theorem id_bijective (A : DividedPowerChainAlgebra.{uR, uA} R) :
    (id A).Bijective := sorry

/-- A composite of degreewise-surjective semilinear divided-power morphisms is surjective. -/
theorem comp_surjective {g : SemilinearHom tau B C} {f : SemilinearHom sigma A B}
    (hg : g.Surjective) (hf : f.Surjective) :
    (comp g f).Surjective := sorry

/-- A composite of degreewise-injective semilinear divided-power morphisms is injective. -/
theorem comp_injective {g : SemilinearHom tau B C} {f : SemilinearHom sigma A B}
    (hg : g.Injective) (hf : f.Injective) :
    (comp g f).Injective := sorry

/-- A composite of degreewise-bijective semilinear divided-power morphisms is bijective. -/
theorem comp_bijective {g : SemilinearHom tau B C} {f : SemilinearHom sigma A B}
    (hg : g.Bijective) (hf : f.Bijective) :
    (comp g f).Bijective := sorry

end SemilinearHom

end DividedPowerChainAlgebra
