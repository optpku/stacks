/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import stacks_project.Chap88.«88_2_0_1_AdicAlgebraSystem»

/-!
# Base change of adic inverse systems of algebras

Given `φ : A₁ →+* A₂` and ideals `Iᵢ` with `Ideal.map φ (I₁ ^ c) ≤ I₂` for some
`c ≥ 1`, this file constructs the functor `C₁ ⥤ C₂` sending a finite-type adic
inverse system `(B n)` over `A₁ ⧸ I₁ ^ n` to the reindexed tensors
`B (c * n) ⊗[A₁ ⧸ I₁ ^ (c * n)] (A₂ ⧸ I₂ ^ n)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.PNatInverseSystem
open scoped TensorProduct

noncomputable section

universe u

namespace AdicAlgebraSystem

/-- Reindex a positive stage `n` by a factor `c ≥ 1`. -/
def stretchIndex {c : ℕ} (hc : 1 ≤ c) (n : ℕ+) : ℕ+ :=
  ⟨c * (n : ℕ), Nat.mul_pos (Nat.succ_le_iff.mp hc) n.pos⟩

/-- The underlying natural number of `stretchIndex hc n` is `c * n`. -/
theorem stretchIndex_coe {c : ℕ} (hc : 1 ≤ c) (n : ℕ+) :
    (stretchIndex hc n : ℕ) = c * (n : ℕ) := sorry

/-- Stretching positive indices is monotone. -/
theorem stretchIndex_mono {c : ℕ} (hc : 1 ≤ c) {m n : ℕ+} (hmn : m ≤ n) :
    stretchIndex hc m ≤ stretchIndex hc n := sorry

/-- A morphism `i ⟶ j` in `OrderDual ℕ+` has `ofDual j ≤ ofDual i`. -/
theorem ofDual_le_of_hom {i j : OrderDual ℕ+} (f : i ⟶ j) :
    OrderDual.ofDual j ≤ OrderDual.ofDual i := sorry

/-- Coercion of a positive inequality to an inequality of underlying naturals. -/
theorem nat_le_of_pnat_le {m n : ℕ+} (h : m ≤ n) : (m : ℕ) ≤ n := sorry

/-- Tensor product of two commutative rings over a common base, given the structure maps. -/
def tensorOver {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) : CommRingCat.{u} :=
  -- Local instance justification (noncanonical choice): `Algebra R A` is the algebra structure of the supplied hom `f`, not a global instance.
  letI := f.toAlgebra
  -- Local instance justification (noncanonical choice): `Algebra R B` is the algebra structure of the supplied hom `g`, not a global instance.
  letI := g.toAlgebra
  CommRingCat.of (A ⊗[R] B)

/-- The right inclusion into `tensorOver f g`. -/
def tensorOverIncludeRight {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) : B →+* tensorOver f g :=
  -- Local instance justification (noncanonical choice): `includeRight` needs the algebra structure of the supplied hom `f`.
  letI := f.toAlgebra
  -- Local instance justification (noncanonical choice): `includeRight` needs the algebra structure of the supplied hom `g`.
  letI := g.toAlgebra
  Algebra.TensorProduct.includeRight.toRingHom

/-- The left inclusion into `tensorOver f g`. -/
def tensorOverIncludeLeft {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) : A →+* tensorOver f g :=
  -- Local instance justification (noncanonical choice): `includeLeftRingHom` needs the algebra structure of the supplied hom `f`.
  letI := f.toAlgebra
  -- Local instance justification (noncanonical choice): `includeLeftRingHom` needs the algebra structure of the supplied hom `g`.
  letI := g.toAlgebra
  Algebra.TensorProduct.includeLeftRingHom

/-- Tensor product of ring homs over a common base. -/
def tensorOverMap {R A B A' B' : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (f : R →+* A) (g : R →+* B) (f' : R →+* A') (g' : R →+* B')
    (hA : A →+* A') (hB : B →+* B') :
    tensorOver f g →+* tensorOver f' g' :=
  -- Local instance justification (noncanonical choice): domain tensor uses the algebra structure of the supplied hom `f`.
  letI := f.toAlgebra
  -- Local instance justification (noncanonical choice): domain tensor uses the algebra structure of the supplied hom `g`.
  letI := g.toAlgebra
  -- Local instance justification (noncanonical choice): codomain tensor uses the algebra structure of the supplied hom `f'`.
  letI := f'.toAlgebra
  -- Local instance justification (noncanonical choice): codomain tensor uses the algebra structure of the supplied hom `g'`.
  letI := g'.toAlgebra
  (Algebra.TensorProduct.map
      ({ hA with commutes' := sorry } : A →ₐ[R] A')
      ({ hB with commutes' := sorry } : B →ₐ[R] B')).toRingHom

/-- Universal map out of `tensorOver f g` induced by a pair of ring homs. -/
def tensorOverLift {R A B C : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    (f : R →+* A) (g : R →+* B) (hA : A →+* C) (hB : B →+* C) :
    tensorOver f g →+* C :=
  -- Local instance justification (noncanonical choice): domain tensor uses the algebra structure of the supplied hom `f`.
  letI := f.toAlgebra
  -- Local instance justification (noncanonical choice): domain tensor uses the algebra structure of the supplied hom `g`.
  letI := g.toAlgebra
  -- Local instance justification (noncanonical choice): the target algebra over `R` is the composite `hA.comp f`, not a global instance.
  letI := (hA.comp f).toAlgebra
  (Algebra.TensorProduct.lift
      ({ hA with commutes' := sorry } : A →ₐ[R] C)
      ({ hB with commutes' := sorry } : B →ₐ[R] C)
      (fun _ _ ↦ Commute.all _ _)).toRingHom

variable {A : Type u} [CommRing A]

/-- The stage ring homomorphism of a morphism of inverse systems of algebras. -/
def stageHom {I : Ideal A} {B B' : Under (quotientSystem I)} (f : B ⟶ B') (n : ℕ+) :
    B.right.stage n →+* B'.right.stage n :=
  (Under.Hom.right f).app (OrderDual.toDual n) |>.hom

/-- The stage algebra homomorphism of a morphism of inverse systems of algebras. -/
def stageAlgHom {I : Ideal A} {B B' : Under (quotientSystem I)} (f : B ⟶ B') (n : ℕ+) :
    B.right.stage n →ₐ[A ⧸ I ^ (n : ℕ)] B'.right.stage n where
  toRingHom := stageHom f n
  commutes' := sorry

variable {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]

/-- The containment `φ(I₁ ^ (c * n)) ⊆ I₂ ^ n` induced by `φ(I₁ ^ c) ⊆ I₂`. -/
theorem map_pow_le (φ : A₁ →+* A₂) (I₁ : Ideal A₁) (I₂ : Ideal A₂)
    {c : ℕ} (hc : 1 ≤ c) (hI : Ideal.map φ (I₁ ^ c) ≤ I₂) (n : ℕ+) :
    Ideal.map φ (I₁ ^ (c * (n : ℕ))) ≤ I₂ ^ (n : ℕ) := sorry

/-- The comap form of `map_pow_le`, as needed by `Ideal.quotientMap`. -/
theorem map_pow_le_comap (φ : A₁ →+* A₂) (I₁ : Ideal A₁) (I₂ : Ideal A₂)
    {c : ℕ} (hc : 1 ≤ c) (hI : Ideal.map φ (I₁ ^ c) ≤ I₂) (n : ℕ+) :
    I₁ ^ (stretchIndex hc n : ℕ) ≤ (I₂ ^ (n : ℕ)).comap φ := sorry

/-- The induced stage maps `A₁ ⧸ I₁ ^ (c * n) →+* A₂ ⧸ I₂ ^ n`. -/
def baseChangeHom (φ : A₁ →+* A₂) (I₁ : Ideal A₁) (I₂ : Ideal A₂)
    {c : ℕ} (hc : 1 ≤ c) (hI : Ideal.map φ (I₁ ^ c) ≤ I₂) (n : ℕ+) :
    A₁ ⧸ I₁ ^ (stretchIndex hc n : ℕ) →+* A₂ ⧸ I₂ ^ (n : ℕ) :=
  Ideal.quotientMap (I₂ ^ (n : ℕ)) φ (map_pow_le_comap φ I₁ I₂ hc hI n)

/-- `baseChangeHom` sends the class of `x` to the class of `φ x`. -/
theorem baseChangeHom_mk (φ : A₁ →+* A₂) (I₁ : Ideal A₁) (I₂ : Ideal A₂)
    {c : ℕ} (hc : 1 ≤ c) (hI : Ideal.map φ (I₁ ^ c) ≤ I₂) (n : ℕ+) (x : A₁) :
    baseChangeHom φ I₁ I₂ hc hI n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (φ x) := sorry

/-- The source-facing stage `B (c * n) ⊗[A₁ ⧸ I₁ ^ (c * n)] (A₂ ⧸ I₂ ^ n)`. -/
def baseChangeStage (φ : A₁ →+* A₂) (I₁ : Ideal A₁) (I₂ : Ideal A₂)
    {c : ℕ} (hc : 1 ≤ c) (hI : Ideal.map φ (I₁ ^ c) ≤ I₂)
    (B : Under (quotientSystem I₁)) (n : ℕ+) : CommRingCat.{u} :=
  tensorOver (stageAlgebraMap I₁ B (stretchIndex hc n))
    (baseChangeHom φ I₁ I₂ hc hI n)

/-- Transition maps of the tensored inverse system. -/
def baseChangeStageMap (φ : A₁ →+* A₂) (I₁ : Ideal A₁) (I₂ : Ideal A₂)
    {c : ℕ} (hc : 1 ≤ c) (hI : Ideal.map φ (I₁ ^ c) ≤ I₂)
    {m n : ℕ+} (hmn : m ≤ n) (B : Under (quotientSystem I₁)) :
    baseChangeStage φ I₁ I₂ hc hI B n ⟶ baseChangeStage φ I₁ I₂ hc hI B m :=
  CommRingCat.ofHom
    (tensorOverLift
      (stageAlgebraMap I₁ B (stretchIndex hc n))
      (baseChangeHom φ I₁ I₂ hc hI n)
      (tensorOverIncludeLeft (stageAlgebraMap I₁ B (stretchIndex hc m))
          (baseChangeHom φ I₁ I₂ hc hI m) |>.comp
        (OrderDualInverseSystem.transitionMap B.right (stretchIndex_mono hc hmn)).hom)
      (tensorOverIncludeRight (stageAlgebraMap I₁ B (stretchIndex hc m))
          (baseChangeHom φ I₁ I₂ hc hI m) |>.comp
        (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (nat_le_of_pnat_le hmn)))))

/-- The inverse system `n ↦ B (c * n) ⊗[A₁ ⧸ I₁ ^ (c * n)] (A₂ ⧸ I₂ ^ n)`. -/
def baseChangeSystem (φ : A₁ →+* A₂) (I₁ : Ideal A₁) (I₂ : Ideal A₂)
    {c : ℕ} (hc : 1 ≤ c) (hI : Ideal.map φ (I₁ ^ c) ≤ I₂)
    (B : Under (quotientSystem I₁)) : PNatInverseSystem CommRingCat.{u} where
  obj i := baseChangeStage φ I₁ I₂ hc hI B (OrderDual.ofDual i)
  map f := baseChangeStageMap φ I₁ I₂ hc hI (ofDual_le_of_hom f) B
  map_id := sorry
  map_comp := sorry

/-- Structure maps `A₂ ⧸ I₂ ^ n → B (c * n) ⊗[A₁ ⧸ I₁ ^ (c * n)] (A₂ ⧸ I₂ ^ n)`. -/
def baseChangeStructure (φ : A₁ →+* A₂) (I₁ : Ideal A₁) (I₂ : Ideal A₂)
    {c : ℕ} (hc : 1 ≤ c) (hI : Ideal.map φ (I₁ ^ c) ≤ I₂)
    (B : Under (quotientSystem I₁)) :
    quotientSystem I₂ ⟶ baseChangeSystem φ I₁ I₂ hc hI B where
  app i :=
    CommRingCat.ofHom
      (tensorOverIncludeRight (stageAlgebraMap I₁ B (stretchIndex hc (OrderDual.ofDual i)))
        (baseChangeHom φ I₁ I₂ hc hI (OrderDual.ofDual i)))
  naturality := sorry

/-- Functoriality of `baseChangeSystem` in morphisms of systems. -/
def baseChangeSystemMap (φ : A₁ →+* A₂) (I₁ : Ideal A₁) (I₂ : Ideal A₂)
    {c : ℕ} (hc : 1 ≤ c) (hI : Ideal.map φ (I₁ ^ c) ≤ I₂)
    {B B' : Under (quotientSystem I₁)} (f : B ⟶ B') :
    baseChangeSystem φ I₁ I₂ hc hI B ⟶ baseChangeSystem φ I₁ I₂ hc hI B' where
  app i :=
    CommRingCat.ofHom
      (tensorOverMap
        (stageAlgebraMap I₁ B (stretchIndex hc (OrderDual.ofDual i)))
        (baseChangeHom φ I₁ I₂ hc hI (OrderDual.ofDual i))
        (stageAlgebraMap I₁ B' (stretchIndex hc (OrderDual.ofDual i)))
        (baseChangeHom φ I₁ I₂ hc hI (OrderDual.ofDual i))
        (stageHom f (stretchIndex hc (OrderDual.ofDual i)))
        (RingHom.id _))
  naturality := sorry

/-- Ambient base change on inverse systems of algebras over the adic quotient towers. -/
def underBaseChange (φ : A₁ →+* A₂) (I₁ : Ideal A₁) (I₂ : Ideal A₂)
    {c : ℕ} (hc : 1 ≤ c) (hI : Ideal.map φ (I₁ ^ c) ≤ I₂) :
    Under (quotientSystem I₁) ⥤ Under (quotientSystem I₂) where
  obj B := Under.mk (baseChangeStructure φ I₁ I₂ hc hI B)
  map f := Under.homMk (baseChangeSystemMap φ I₁ I₂ hc hI f) sorry
  map_id := sorry
  map_comp := sorry

/-- The image of an object of `C₁` under stagewise tensor satisfies the object conditions of `C₂`. -/
instance instIsObjectUnderBaseChange (φ : A₁ →+* A₂) (I₁ : Ideal A₁) (I₂ : Ideal A₂)
    {c : ℕ} (hc : 1 ≤ c) (hI : Ideal.map φ (I₁ ^ c) ≤ I₂)
    (B : Under (quotientSystem I₁)) [IsObject I₁ B] :
    IsObject I₂ ((underBaseChange φ I₁ I₂ hc hI).obj B) := sorry

/-- The base-change functor `C₁ ⥤ C₂` sending `(B n)` to
`B (c * n) ⊗[A₁ ⧸ I₁ ^ (c * n)] (A₂ ⧸ I₂ ^ n)`. -/
def baseChange (φ : A₁ →+* A₂) (I₁ : Ideal A₁) (I₂ : Ideal A₂)
    {c : ℕ} (hc : 1 ≤ c) (hI : Ideal.map φ (I₁ ^ c) ≤ I₂) :
    AdicAlgebraSystem A₁ I₁ ⥤ AdicAlgebraSystem A₂ I₂ where
  obj B := of A₂ I₂ ((underBaseChange φ I₁ I₂ hc hI).obj B.obj)
  map f := ofHom ((underBaseChange φ I₁ I₂ hc hI).map f.hom)
  map_id := sorry
  map_comp := sorry

/-- The underlying inverse system of `baseChange.obj B` has stages the source tensor formula. -/
theorem baseChange_obj (φ : A₁ →+* A₂) (I₁ : Ideal A₁) (I₂ : Ideal A₂)
    {c : ℕ} (hc : 1 ≤ c) (hI : Ideal.map φ (I₁ ^ c) ≤ I₂)
    (B : AdicAlgebraSystem A₁ I₁) (n : ℕ+) :
    ((baseChange φ I₁ I₂ hc hI).obj B).obj.right.stage n =
      baseChangeStage φ I₁ I₂ hc hI B.obj n := sorry

/-- Stage maps of `baseChange.map f` are the tensor product of the system map at `c * n` with `id`. -/
theorem baseChange_map (φ : A₁ →+* A₂) (I₁ : Ideal A₁) (I₂ : Ideal A₂)
    {c : ℕ} (hc : 1 ≤ c) (hI : Ideal.map φ (I₁ ^ c) ≤ I₂)
    {B B' : AdicAlgebraSystem A₁ I₁} (f : B ⟶ B') (n : ℕ+) :
    (Under.Hom.right ((baseChange φ I₁ I₂ hc hI).map f).hom).app (OrderDual.toDual n) =
      CommRingCat.ofHom
        (tensorOverMap
          (stageAlgebraMap I₁ B.obj (stretchIndex hc n))
          (baseChangeHom φ I₁ I₂ hc hI n)
          (stageAlgebraMap I₁ B'.obj (stretchIndex hc n))
          (baseChangeHom φ I₁ I₂ hc hI n)
          (stageHom f.hom (stretchIndex hc n))
          (RingHom.id _)) := sorry

/-- Stages of the image system are finite type over `A₂ ⧸ I₂ ^ n`. -/
theorem preservesFiniteType (φ : A₁ →+* A₂) (I₁ : Ideal A₁) (I₂ : Ideal A₂)
    {c : ℕ} (hc : 1 ≤ c) (hI : Ideal.map φ (I₁ ^ c) ≤ I₂)
    (B : AdicAlgebraSystem A₁ I₁) (n : ℕ+) :
    (stageAlgebraMap I₂ ((baseChange φ I₁ I₂ hc hI).obj B).obj n).FiniteType := sorry

/-- Successor maps of the image system induce `B'_{n+1} ⧸ I₂ ^ n B'_{n+1} ≅ B'ₙ`. -/
theorem preservesStepIso (φ : A₁ →+* A₂) (I₁ : Ideal A₁) (I₂ : Ideal A₂)
    {c : ℕ} (hc : 1 ≤ c) (hI : Ideal.map φ (I₁ ^ c) ≤ I₂)
    (B : AdicAlgebraSystem A₁ I₁) (n : ℕ+) :
    Function.Bijective
      (stepQuotientHom I₂ ((baseChange φ I₁ I₂ hc hI).obj B).obj n) := sorry

end AdicAlgebraSystem
