module

public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Constructions

/-!
# Completed tensor product of linearly topologized algebras

The completed tensor product of linearly topologized algebras `A` and `B` over `R` is the inverse
limit of the stage tensors `(A ⧸ I) ⊗[R] (B ⧸ J)` as `I` and `J` run through open ideals. This is
the ring-level counterpart of `TensorProduct.Completed`, with pointwise ring operations on stages.
Open ideals are cofinal among open submodules, and the explicit comparison
`Algebra.TensorProduct.Completed.equivModuleCompleted` with the module-level object lives in
`ReasLib.Topology.Algebra.TensorProduct.CompletedRing.ModuleComparison`.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

namespace Algebra.TensorProduct

variable (R A B : Type u)
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable [TopologicalSpace A] [TopologicalSpace B]

/-- The completed tensor product of linearly topologized algebras, realized as the inverse
limit of the stage tensors `(A ⧸ I) ⊗[R] (B ⧸ J)` over open ideals `I ⊆ A` and `J ⊆ B`. -/
def Completed : Type u :=
  { f : ∀ (I : {I : Ideal A // IsOpen (I : Set A)})
      (J : {J : Ideal B // IsOpen (J : Set B)}),
      (A ⧸ I.1) ⊗[R] (B ⧸ J.1) //
    ∀ (I I' : {I : Ideal A // IsOpen (I : Set A)})
      (J J' : {J : Ideal B // IsOpen (J : Set B)})
      (hII' : I.1 ≤ I'.1) (hJJ' : J.1 ≤ J'.1),
      map (Ideal.Quotient.factorₐ R hII') (Ideal.Quotient.factorₐ R hJJ') (f I J) = f I' J' }

namespace Completed

/-- Zero in the completed tensor product is the zero family of stage tensors. -/
instance instZero : Zero (Completed R A B) where
  zero := ⟨0, by
    intro ideal ideal' quotient quotient' hIdeal hQuotient
    exact map_zero _⟩

/-- One in the completed tensor product is the unit family of stage tensors. -/
instance instOne : One (Completed R A B) where
  one := ⟨1, by
    intro ideal ideal' quotient quotient' hIdeal hQuotient
    exact map_one _⟩

/-- Pointwise addition of compatible families of stage tensors. -/
instance instAdd : Add (Completed R A B) where
  add x y := ⟨x.1 + y.1, by
    intro ideal ideal' quotient quotient' hIdeal hQuotient
    change map (Ideal.Quotient.factorₐ R hIdeal)
      (Ideal.Quotient.factorₐ R hQuotient) (x.1 ideal quotient + y.1 ideal quotient) =
        x.1 ideal' quotient' + y.1 ideal' quotient'
    simpa only [map_add] using congrArg₂ (· + ·)
      (x.2 ideal ideal' quotient quotient' hIdeal hQuotient)
      (y.2 ideal ideal' quotient quotient' hIdeal hQuotient)⟩

/-- Pointwise multiplication of compatible families of stage tensors. -/
instance instMul : Mul (Completed R A B) where
  mul x y := ⟨x.1 * y.1, by
    intro ideal ideal' quotient quotient' hIdeal hQuotient
    change map (Ideal.Quotient.factorₐ R hIdeal)
      (Ideal.Quotient.factorₐ R hQuotient) (x.1 ideal quotient * y.1 ideal quotient) =
        x.1 ideal' quotient' * y.1 ideal' quotient'
    simpa only [map_mul] using congrArg₂ (· * ·)
      (x.2 ideal ideal' quotient quotient' hIdeal hQuotient)
      (y.2 ideal ideal' quotient quotient' hIdeal hQuotient)⟩

/-- Pointwise negation of compatible families of stage tensors. -/
instance instNeg : Neg (Completed R A B) where
  neg x := ⟨-x.1, by
    intro ideal ideal' quotient quotient' hIdeal hQuotient
    change map (Ideal.Quotient.factorₐ R hIdeal)
      (Ideal.Quotient.factorₐ R hQuotient) (-x.1 ideal quotient) =
        -x.1 ideal' quotient'
    simpa only [map_neg] using congrArg Neg.neg
      (x.2 ideal ideal' quotient quotient' hIdeal hQuotient)⟩

/-- Pointwise subtraction of compatible families of stage tensors. -/
instance instSub : Sub (Completed R A B) where
  sub x y := ⟨x.1 - y.1, by
    intro ideal ideal' quotient quotient' hIdeal hQuotient
    change map (Ideal.Quotient.factorₐ R hIdeal)
      (Ideal.Quotient.factorₐ R hQuotient) (x.1 ideal quotient - y.1 ideal quotient) =
        x.1 ideal' quotient' - y.1 ideal' quotient'
    simpa only [map_sub] using congrArg₂ (· - ·)
      (x.2 ideal ideal' quotient quotient' hIdeal hQuotient)
      (y.2 ideal ideal' quotient quotient' hIdeal hQuotient)⟩

/-- Natural-number scalar multiplication on compatible families of stage tensors. -/
instance instNSmul : SMul ℕ (Completed R A B) where
  smul n x := ⟨n • x.1, by
    intro ideal ideal' quotient quotient' hIdeal hQuotient
    change map (Ideal.Quotient.factorₐ R hIdeal)
      (Ideal.Quotient.factorₐ R hQuotient) (n • x.1 ideal quotient) =
        n • x.1 ideal' quotient'
    simpa only [map_nsmul] using congrArg (n • ·)
      (x.2 ideal ideal' quotient quotient' hIdeal hQuotient)⟩

/-- Integer scalar multiplication on compatible families of stage tensors. -/
instance instZSmul : SMul ℤ (Completed R A B) where
  smul n x := ⟨n • x.1, by
    intro ideal ideal' quotient quotient' hIdeal hQuotient
    change map (Ideal.Quotient.factorₐ R hIdeal)
      (Ideal.Quotient.factorₐ R hQuotient) (n • x.1 ideal quotient) =
        n • x.1 ideal' quotient'
    simpa only [map_zsmul] using congrArg (n • ·)
      (x.2 ideal ideal' quotient quotient' hIdeal hQuotient)⟩

/-- Pointwise natural-number powers of compatible families of stage tensors. -/
instance instPow : Pow (Completed R A B) ℕ where
  pow x n := ⟨x.1 ^ n, by
    intro ideal ideal' quotient quotient' hIdeal hQuotient
    change map (Ideal.Quotient.factorₐ R hIdeal)
      (Ideal.Quotient.factorₐ R hQuotient) (x.1 ideal quotient ^ n) =
        x.1 ideal' quotient' ^ n
    simpa only [map_pow] using congrArg (· ^ n)
      (x.2 ideal ideal' quotient quotient' hIdeal hQuotient)⟩

/-- Natural-number cast of compatible families of stage tensors. -/
instance instNatCast : NatCast (Completed R A B) where
  natCast n := ⟨n, by
    intro ideal ideal' quotient quotient' hIdeal hQuotient
    exact map_natCast _ n⟩

/-- Integer cast of compatible families of stage tensors. -/
instance instIntCast : IntCast (Completed R A B) where
  intCast n := ⟨n, by
    intro ideal ideal' quotient quotient' hIdeal hQuotient
    exact map_intCast _ n⟩

/-- The completed tensor product is a commutative ring under pointwise operations. -/
instance instCommRing : CommRing (Completed R A B) :=
  Subtype.val_injective.commRing (fun x : Completed R A B ↦ x.1)
    rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- The inverse-limit topology on the completed tensor product, induced from the product of
discrete topologies on the stage tensors. -/
instance instTopologicalSpace : TopologicalSpace (Completed R A B) :=
  TopologicalSpace.induced Subtype.val <|
    ⨅ (I : {I : Ideal A // IsOpen (I : Set A)})
      (J : {J : Ideal B // IsOpen (J : Set B)}),
      TopologicalSpace.induced (fun f ↦ f I J)
        (⊥ : TopologicalSpace ((A ⧸ I.1) ⊗[R] (B ⧸ J.1)))

/-- Canonical ring homomorphism from the algebraic tensor product into the completed tensor. -/
def of : A ⊗[R] B →+* Completed R A B where
  toFun x :=
    ⟨fun I J ↦ map (Ideal.Quotient.mkₐ R I.1) (Ideal.Quotient.mkₐ R J.1) x, by
      intro ideal ideal' quotient quotient' hIdeal hQuotient
      change ((map (Ideal.Quotient.factorₐ R hIdeal)
        (Ideal.Quotient.factorₐ R hQuotient)).comp
          (map (Ideal.Quotient.mkₐ R ideal.1) (Ideal.Quotient.mkₐ R quotient.1))) x = _
      rw [← map_comp, Ideal.Quotient.factorₐ_comp_mk, Ideal.Quotient.factorₐ_comp_mk]⟩
  map_one' := by
    apply Subtype.ext
    funext ideal quotient
    exact map_one _
  map_mul' := by
    intro left right
    apply Subtype.ext
    funext ideal quotient
    exact map_mul _ left right
  map_zero' := by
    apply Subtype.ext
    funext ideal quotient
    exact map_zero _
  map_add' := by
    intro left right
    apply Subtype.ext
    funext ideal quotient
    exact map_add _ left right

/-- Projection from the completed tensor product onto the stage `(A ⧸ I) ⊗[R] (B ⧸ J)`. -/
def π (I : Ideal A) (J : Ideal B) (hI : IsOpen (I : Set A)) (hJ : IsOpen (J : Set B)) :
    Completed R A B →+* (A ⧸ I) ⊗[R] (B ⧸ J) where
  toFun f := f.1 ⟨I, hI⟩ ⟨J, hJ⟩
  map_one' := rfl
  map_mul' := fun _ _ ↦ rfl
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl

/-- Canonical ring homomorphism from the left factor into the completed tensor product. -/
def includeLeft : A →+* Completed R A B :=
  (of R A B).comp (includeLeftRingHom : A →+* A ⊗[R] B)

/-- Canonical ring homomorphism from the right factor into the completed tensor product. -/
def includeRight : B →+* Completed R A B :=
  (of R A B).comp (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom

/-- The completed tensor product is an `R`-algebra via `Completed.of`. -/
instance instAlgebra : Algebra R (Completed R A B) :=
  ((of R A B).comp (algebraMap R (A ⊗[R] B))).toAlgebra

/-- Compatibility of a completed tensor with the inverse system of stage tensors. -/
theorem compatible (f : Completed R A B) (I I' : Ideal A) (J J' : Ideal B)
    (hI : IsOpen (I : Set A)) (hI' : IsOpen (I' : Set A))
    (hJ : IsOpen (J : Set B)) (hJ' : IsOpen (J' : Set B))
    (hII' : I ≤ I') (hJJ' : J ≤ J') :
    map (Ideal.Quotient.factorₐ R hII') (Ideal.Quotient.factorₐ R hJJ')
      (π R A B I J hI hJ f) = π R A B I' J' hI' hJ' f := sorry

/-- The canonical map to the completion, evaluated at a stage, is the stage quotient map. -/
theorem π_of (I : Ideal A) (J : Ideal B)
    (hI : IsOpen (I : Set A)) (hJ : IsOpen (J : Set B)) (x : A ⊗[R] B) :
    π R A B I J hI hJ (of R A B x) =
      map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R J) x := sorry

/-- The right inclusion sends `b` to the image of `1 ⊗ₜ b` under `Completed.of`. -/
theorem includeRight_apply (b : B) :
    includeRight R A B b = of R A B (1 ⊗ₜ b) := sorry

/-- If the left factor is a topological ring, its canonical map into the completed tensor
product is continuous. -/
theorem continuous_includeLeft [IsTopologicalRing A] :
    Continuous (includeLeft R A B) := sorry

/-- If the right factor is a topological ring, its canonical map into the completed tensor
product is continuous. -/
theorem continuous_includeRight [IsTopologicalRing B] :
    Continuous (includeRight R A B) := sorry

variable [IsTopologicalRing A] [IsTopologicalRing B]
variable [IsLinearTopology A A] [IsLinearTopology B B]

/-- Addition, multiplication, and negation are continuous on the completed tensor product. -/
instance instIsTopologicalRing : IsTopologicalRing (Completed R A B) := sorry

/-- The completed tensor product is linearly topologized as a module over itself. -/
instance instIsLinearTopology : IsLinearTopology (Completed R A B) (Completed R A B) := sorry

end Completed

end Algebra.TensorProduct
