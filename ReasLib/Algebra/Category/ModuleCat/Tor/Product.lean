module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.CohomologyProduct
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence
public import ReasLib.Algebra.Category.ModuleCat.Tor.Notation
public import ReasLib.Algebra.Category.ModuleCat.Tor.TensorAction
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.CrossRefAttribute

/-!
# Products on Tor

The product on `Tor⁽*⁾[R](B, A)` is obtained from the cohomology product on the derived tensor
object `B[0] ⊗[R]^L A[0]`.  The construction layer accepts an explicit monoidal derived-tensor
model; the source-facing product uses the canonical strong-localization model.

@stack 068K
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ModuleCat
open ModuleCat.MonoidalCategory
open scoped DerivedTensorProduct TensorProduct ModuleTor

universe u

-- Local instance justification (instance diamond): select the standard derived-category model
-- only for the Tor product construction.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModuleCat.Tor.Product

variable {R : Type u} [CommRing R]
variable {A : Type u} [CommRing A] [Algebra R A]
variable [MonoidalCategory (DerivedCategory (ModuleCat R))]
variable [BraidedCategory (DerivedCategory (ModuleCat R))]
variable [(DerivedCategory.Qh : HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ) ⥤
    DerivedCategory (ModuleCat R)).Monoidal]
variable [(DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤
    DerivedCategory (ModuleCat R)).Monoidal]

local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)
set_option quotPrecheck false in
local notation "TorA(" n ")" => ((CategoryTheory.Tor (ModuleCat R) n).flip.obj (of R A))

variable (A)

/-- The canonical strong-localization model relating the ambient monoidal product to the
fixed-right derived tensor product. -/
@[stacks 068K "canonical monoidal model for the Tor product"]
noncomputable def model :
    DerivedCategory.DerivedTensor.Right.Monoidal.Model (C := ModuleCat R) :=
  DerivedCategory.DerivedTensor.Right.Monoidal.Strong.modelFamily

/-- Addition of negative cohomological degrees corresponds to addition of Tor degrees. -/
@[stacks 068K "Tor product degree reindexing"]
theorem degree_eq (n m : ℕ) :
    (-(n : ℤ) + -(m : ℤ)) = -((n + m : ℕ) : ℤ) := sorry

/-- Right tensoring a degree-zero single complex remains a degree-zero single complex. -/
@[stacks 068K "right tensor comparison for degree-zero complexes"]
noncomputable def singleRightComplexIso (M N : ModuleCat R) :
    ((MonoidalCategory.tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) ≅
      (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj
        (of R ((↑M) ⊗[R] ↑N)) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (MonoidalCategory.tensorRight N) (ComplexShape.up ℤ) (0 : ℤ)).app M

/-- The tensor complex of two degree-zero single complexes is the single complex on their
ordinary tensor product. -/
@[stacks 068K "degree-zero tensor-complex identification"]
theorem singleComplex_eq_tensorObj (M N : ModuleCat R) :
    (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj
        (of R ((↑M) ⊗[R] ↑N)) =
      HomologicalComplex.tensorObj
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N) := sorry

/-- Compare the derived tensor of two degree-zero modules with their ordinary tensor product,
using an explicit ambient monoidal model. -/
@[stacks 068K "derived tensor comparison for degree-zero modules"]
noncomputable def singleDerivedTensorIsoOf
    (T : DerivedCategory.DerivedTensor.Right.Monoidal.Model (C := ModuleCat R))
    (M N : ModuleCat R) :
    (Functor.obj single₀ M ⊗[R]^L Functor.obj single₀ N) ≅
      Functor.obj single₀ (of R ((↑M) ⊗[R] ↑N)) :=
  T.objIsoTensor (Functor.obj single₀ M) (Functor.obj single₀ N) ≪≫
    (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app M) ⊗ᵢ
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app N)) ≪≫
    (Functor.Monoidal.μIso (DerivedCategory.Q : Cpx ⥤ DMod)
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)) ≪≫
    (DerivedCategory.Q.mapIso (eqToIso (singleComplex_eq_tensorObj M N))).symm ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
      (of R ((↑M) ⊗[R] ↑N))).symm

/-- Compare the ambient tensor of two degree-zero derived objects with the ordinary tensor
product, using an explicit ambient monoidal model. -/
@[stacks 068K "monoidal tensor comparison for degree-zero modules"]
noncomputable def singleTensorIsoOf
    (T : DerivedCategory.DerivedTensor.Right.Monoidal.Model (C := ModuleCat R))
    (M N : ModuleCat R) :
    (Functor.obj single₀ M ⊗ Functor.obj single₀ N) ≅
      Functor.obj single₀ (of R ((↑M) ⊗[R] ↑N)) :=
  (T.objIsoTensor (Functor.obj single₀ M) (Functor.obj single₀ N)).symm ≪≫
    singleDerivedTensorIsoOf T M N

/-- Reindex the target of the cohomology product from degree `-n + -m` to degree `-(n + m)`. -/
@[stacks 068K "Tor product target reindexing"]
theorem reindex (B : Type u) [CommRing B] [Algebra R B] (n m : ℕ) :
    (H (-(n : ℤ) + -(m : ℤ))).obj
        ((Functor.obj single₀ (of R B) ⊗[R]^L Functor.obj single₀ (of R A)) ⊗[R]^L
          (Functor.obj single₀ (of R B) ⊗[R]^L Functor.obj single₀ (of R A))) =
      (H (-((n + m : ℕ) : ℤ))).obj
        ((Functor.obj single₀ (of R B) ⊗[R]^L Functor.obj single₀ (of R A)) ⊗[R]^L
          (Functor.obj single₀ (of R B) ⊗[R]^L Functor.obj single₀ (of R A))) := sorry

/-- Identify Tor with the homology of the derived tensor of degree-zero module objects. -/
@[stacks 068K "Tor as homology of a single-object derived tensor"]
theorem obj_eq_homology_singleTensor
    (B : Type u) [CommRing B] [Algebra R B] (n : ℕ) :
    Tor⁽n⁾[R](B, A) =
      (H (-(n : ℤ))).obj
        (Functor.obj single₀ (of R B) ⊗[R]^L Functor.obj single₀ (of R A)) := sorry

/-- The comparison isomorphism from Tor to the homology of the corresponding derived tensor. -/
@[stacks 068K "Tor-single-derived-tensor comparison"]
noncomputable abbrev objIsoHomologySingleTensor
    (B : Type u) [CommRing B] [Algebra R B] (n : ℕ) :
    Tor⁽n⁾[R](B, A) ≅
      (H (-(n : ℤ))).obj
        (Functor.obj single₀ (of R B) ⊗[R]^L Functor.obj single₀ (of R A)) :=
  eqToIso (obj_eq_homology_singleTensor A B n)

/-- Multiplication on `B[0] ⊗[R]^L A[0]`, assembled using an explicit monoidal model and the
ordinary multiplication maps of `B` and `A`. -/
@[stacks 068K "derived multiplication underlying the Tor product"]
noncomputable def derivedMultiplicationOf
    (T : DerivedCategory.DerivedTensor.Right.Monoidal.Model (C := ModuleCat R))
    (B : Type u) [CommRing B] [Algebra R B] :
    let B0 : DMod := Functor.obj single₀ (of R B)
    let A0 : DMod := Functor.obj single₀ (of R A)
    let torObj : DMod := B0 ⊗[R]^L A0
    torObj ⊗[R]^L torObj ⟶ torObj :=
  let B0 : DMod := Functor.obj single₀ (of R B)
  let A0 : DMod := Functor.obj single₀ (of R A)
  let torObj : DMod := B0 ⊗[R]^L A0
  let μB : Functor.obj single₀ (of R (B ⊗[R] B)) ⟶ B0 :=
    Functor.map single₀
      (ofHom ((Algebra.TensorProduct.productMap
        (AlgHom.id R B) (AlgHom.id R B)).toLinearMap))
  let μA : Functor.obj single₀ (of R (A ⊗[R] A)) ⟶ A0 :=
    Functor.map single₀
      (ofHom ((Algebra.TensorProduct.productMap
        (AlgHom.id R A) (AlgHom.id R A)).toLinearMap))
  (T.objIsoTensor torObj torObj).hom ≫
    ((T.objIsoTensor B0 A0).hom ⊗ₘ (T.objIsoTensor B0 A0).hom) ≫
    (α_ B0 A0 (B0 ⊗ A0)).hom ≫
    (𝟙 B0 ⊗ₘ (α_ A0 B0 A0).inv) ≫
    (𝟙 B0 ⊗ₘ ((β_ A0 B0).hom ⊗ₘ 𝟙 A0)) ≫
    (𝟙 B0 ⊗ₘ (α_ B0 A0 A0).hom) ≫
    (α_ B0 B0 (A0 ⊗ A0)).inv ≫
    ((singleTensorIsoOf T (of R B) (of R B)).hom ⊗ₘ
      (singleTensorIsoOf T (of R A) (of R A)).hom) ≫
    (μB ⊗ₘ μA) ≫
    (T.objIsoTensor B0 A0).inv

/-- The Tor product constructed from an explicit ambient monoidal derived-tensor model. -/
@[stacks 068K "Tor product from an explicit derived-tensor model"]
noncomputable def mulOf
    (T : DerivedCategory.DerivedTensor.Right.Monoidal.Model (C := ModuleCat R))
    (B : Type u) [CommRing B] [Algebra R B] (n m : ℕ) :
    (Tor⁽n⁾[R](B, A) ⊗ Tor⁽m⁾[R](B, A) : ModuleCat R) ⟶
      Tor⁽n + m⁾[R](B, A) :=
  let torObj : DMod :=
    Functor.obj single₀ (of R B) ⊗[R]^L Functor.obj single₀ (of R A)
  ((objIsoHomologySingleTensor A B n).hom ⊗ₘ
      (objIsoHomologySingleTensor A B m).hom) ≫
    derivedCohomologyProduct T (-(n : ℤ)) (-(m : ℤ)) torObj torObj ≫
    eqToHom (reindex A B n m) ≫
      (H (-((n + m : ℕ) : ℤ))).map (derivedMultiplicationOf A T B) ≫
        (objIsoHomologySingleTensor A B (n + m)).inv

/-- The canonical product on `Tor⁽*⁾[R](B, A)`. -/
@[stacks 068K "canonical Tor product"]
noncomputable def mul (B : Type u) [CommRing B] [Algebra R B] (n m : ℕ) :
    (Tor⁽n⁾[R](B, A) ⊗ Tor⁽m⁾[R](B, A) : ModuleCat R) ⟶
      Tor⁽n + m⁾[R](B, A) :=
  mulOf A (model (R := R)) B n m

/-- The canonical degree-zero unit map induced by the structure map `R →ₐ[R] B`. -/
@[stacks 068K "canonical Tor unit"]
abbrev unit (B : Type u) [CommRing B] [Algebra R B] :
    Tor⁽0⁾[R](R, A) ⟶ Tor⁽0⁾[R](B, A) :=
  (TorA(0)).map (ofHom (Algebra.ofId R B).toLinearMap)

section FirstVariableMaps

variable {B C : Type u} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
variable (g : B →ₐ[R] C)

/-- Lemma 15.63.1 (1): the first-variable map on Tor preserves products. -/
@[stacks 068K "first-variable Tor map preserves products"]
theorem map_mul (n m : ℕ) :
    CommSq
      (((TorA(n)).map (ofHom g.toLinearMap)) ⊗ₘ
        ((TorA(m)).map (ofHom g.toLinearMap)))
      (mul A B n m) (mul A C n m)
      ((TorA(n + m)).map (ofHom g.toLinearMap)) := sorry

/-- Lemma 15.63.1 (2): the first-variable map on Tor preserves the degree-zero unit. -/
@[stacks 068K "first-variable Tor map preserves the unit"]
theorem map_unit :
    unit A C = unit A B ≫ (TorA(0)).map (ofHom g.toLinearMap) := sorry

/-- Lemma 15.63.1 (3): the first-variable map on Tor is linear for the action of the second
algebra `A`. -/
@[stacks 068K "first-variable Tor map is linear over the second algebra"]
theorem map_scalar (n : ℕ) (a : A) (x : Tor⁽n⁾[R](B, A)) :
    ((TorA(n)).map (ofHom g.toLinearMap)).hom
        (TensorAction.rightScalar (R := R) (A := B) (B := A) n a x) =
      TensorAction.rightScalar (R := R) (A := C) (B := A) n a
        (((TorA(n)).map (ofHom g.toLinearMap)).hom x) := sorry

/-- Lemma 15.63.1: the first-variable map on `Tor⁽*⁾[R](-, A)` preserves the canonical product
and unit, the product-and-unit form of the induced graded `A`-algebra homomorphism. -/
@[stacks 068K "first-variable Tor map preserves product and unit"]
theorem map_preserves_mul_and_unit :
    (∀ n m : ℕ,
      CommSq
        (((TorA(n)).map (ofHom g.toLinearMap)) ⊗ₘ
          ((TorA(m)).map (ofHom g.toLinearMap)))
        (mul A B n m) (mul A C n m)
        ((TorA(n + m)).map (ofHom g.toLinearMap))) ∧
      unit A C = unit A B ≫ (TorA(0)).map (ofHom g.toLinearMap) := sorry

end FirstVariableMaps

end CategoryTheory.ModuleCat.Tor.Product
