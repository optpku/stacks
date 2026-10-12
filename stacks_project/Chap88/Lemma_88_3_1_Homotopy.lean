/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.MvPolynomial.Eval
public import stacks_project.Chap88.«88_3_0_1_NaiveCotangent»

/-!
# Homotopy comparison of completed naive cotangent complexes

This leaf owns morphisms of completed polynomial presentations, the induced
maps of two-term Jacobian complexes, and the canonical homotopy equivalence
comparing any two presentations of the same algebra.
-/

@[expose] public section

open CategoryTheory
open Algebra.Extension

noncomputable section

universe u

namespace Algebra.NaiveCotangent.Adic

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {I : Ideal A} {ι ι' ι'' : Type u}

namespace Presentation

/-- A morphism of completed polynomial presentations, given by lifts of the
source variables to the target completed polynomial ring. -/
structure Hom (P : Presentation A B I ι) (Q : Presentation A B I ι') where
  /-- Chosen lifts `g_i` of the images of the source variables `x_i`. -/
  val : ι → polynomialCompletion A I ι'
  /-- Each lift maps to the same element of `B` as the corresponding source variable. -/
  aeval_val :
    ∀ i, Q.toAlgHom (val i) =
      P.toAlgHom
        (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) (MvPolynomial.X i))

variable {P : Presentation A B I ι} {Q : Presentation A B I ι'}
variable {T : Presentation A B I ι''}

/-- The distinguished morphism of presentations obtained by lifting the images
of the source variables along the target surjection. -/
def defaultHom (P : Presentation A B I ι) (Q : Presentation A B I ι') : Hom P Q where
  val i :=
    Function.surjInv Q.surjective
      (P.toAlgHom
        (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) (MvPolynomial.X i)))
  aeval_val _ := Function.surjInv_eq Q.surjective _

/-- The structure map of `defaultHom` is a chosen lift of the image of each
source variable. -/
theorem defaultHom_val (P : Presentation A B I ι) (Q : Presentation A B I ι') (i : ι) :
    (defaultHom P Q).val i =
      Function.surjInv Q.surjective
        (P.toAlgHom
          (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) (MvPolynomial.X i))) :=
  sorry

namespace Hom

/-- Finite-stage evaluation of a presentation morphism, sending a completed
polynomial to the residue of its evaluation at the chosen lifts. -/
theorem toAlgHomStage_aeval_ker (f : Hom P Q) (n : ℕ) (g : MvPolynomial ι A)
    (hg : g ∈ polynomialIdeal A I ι ^ n) :
    (MvPolynomial.aeval fun i ↦
          AdicCompletion.evalₐ (polynomialIdeal A I ι') n (f.val i) : MvPolynomial ι A →ₐ[A] _) g =
      0 :=
  sorry

/-- Stage-`n` evaluation of a completed polynomial along a morphism of presentations. -/
def toAlgHomStage (f : Hom P Q) (n : ℕ) :
    polynomialCompletion A I ι →ₐ[A] MvPolynomial ι' A ⧸ polynomialIdeal A I ι' ^ n :=
  (Ideal.Quotient.liftₐ (polynomialIdeal A I ι ^ n)
      (MvPolynomial.aeval fun i ↦
        AdicCompletion.evalₐ (polynomialIdeal A I ι') n (f.val i))
      (toAlgHomStage_aeval_ker f n)).comp
    ((AdicCompletion.evalₐ (polynomialIdeal A I ι) n).restrictScalars A)

/-- Finite-stage evaluations of a presentation morphism are compatible with the
inverse system of quotients. -/
theorem toAlgHomStage_compatible (f : Hom P Q) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp (toAlgHomStage f n) =
      toAlgHomStage f m :=
  sorry

/-- The unique continuous `A`-algebra map `A[x_ι]^∧ →ₐ[A] A[y_ι']^∧` sending
each source variable to the chosen lift. -/
def toAlgHom (f : Hom P Q) :
    polynomialCompletion A I ι →ₐ[A] polynomialCompletion A I ι' :=
  AdicCompletion.liftAlgHom (polynomialIdeal A I ι') (fun n ↦ toAlgHomStage f n)
    (fun hle ↦ toAlgHomStage_compatible f hle)

/-- Completed evaluation along a presentation morphism sends the image of each
source variable to the chosen lift. -/
theorem toAlgHom_val (f : Hom P Q) (i : ι) :
    f.toAlgHom
        (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) (MvPolynomial.X i)) =
      f.val i :=
  sorry

/-- A morphism of presentations is compatible with the two structure maps to `B`. -/
theorem toAlgHom_commutes (f : Hom P Q) (x : polynomialCompletion A I ι) :
    Q.toAlgHom (f.toAlgHom x) = P.toAlgHom x :=
  sorry

/-- The algebra-map compatibility needed to view a presentation morphism as a
morphism of extensions. -/
theorem toExtensionHom_commutes (f : Hom P Q) :
    (IsScalarTower.toAlgHom A Q.toExtension.Ring B).comp f.toAlgHom =
      (IsScalarTower.toAlgHom A B B).comp
        (IsScalarTower.toAlgHom A P.toExtension.Ring B) :=
  sorry

/-- The morphism of algebra extensions induced by a morphism of completed
polynomial presentations. -/
def toExtensionHom (f : Hom P Q) : P.toExtension.Hom Q.toExtension :=
  Extension.Hom.ofAlgHom f.toAlgHom (toExtensionHom_commutes f)

/-- The identity morphism of a completed polynomial presentation. -/
protected def id (P : Presentation A B I ι) : Hom P P where
  val i := AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) (MvPolynomial.X i)
  aeval_val _ := rfl

/-- The identity presentation morphism induces the identity algebra map. -/
theorem toAlgHom_id (P : Presentation A B I ι) :
    (Hom.id P).toAlgHom = AlgHom.id A (polynomialCompletion A I ι) :=
  sorry

/-- Compatibility of composed presentation morphisms with the structure maps to `B`. -/
theorem comp_aeval_val (f : Hom Q T) (g : Hom P Q) (i : ι) :
    T.toAlgHom (f.toAlgHom (g.val i)) =
      P.toAlgHom
        (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) (MvPolynomial.X i)) :=
  sorry

/-- Composition of morphisms of completed polynomial presentations. -/
def comp (f : Hom Q T) (g : Hom P Q) : Hom P T where
  val i := f.toAlgHom (g.val i)
  aeval_val := comp_aeval_val f g

/-- The value of a composite presentation morphism is evaluation of the first
lift along the second algebra map. -/
theorem comp_val (f : Hom Q T) (g : Hom P Q) (i : ι) :
    (f.comp g).val i = f.toAlgHom (g.val i) :=
  sorry

/-- Parallel lifts of the same source variable differ by an element of the
target kernel. -/
theorem val_sub_mem_ker (f g : Hom P Q) (i : ι) : f.val i - g.val i ∈ Q.ker :=
  sorry

/-- The Jacobian matrix of a morphism of presentations, acting on the free
module of Kähler generators. -/
def jacobianOnVars [Fintype ι] (f : Hom P Q) : (ι → B) →ₗ[B] (ι' → B) :=
  LinearMap.pi fun j ↦
    ∑ i, LinearMap.smulRight (LinearMap.proj i) (Q.toAlgHom (pderiv I j (f.val i)))

/-- The Jacobian of a presentation morphism is given on coordinates by completed
partials of the chosen lifts. -/
theorem jacobianOnVars_apply [Fintype ι] (f : Hom P Q) (dx : ι → B) (j : ι') :
    jacobianOnVars f dx j = ∑ i, dx i * Q.toAlgHom (pderiv I j (f.val i)) :=
  sorry

/-- The contracting homotopy component sending `dx_i` to the class of
`g_i - x_i` in the target conormal module. -/
def contraction [Fintype ι] (f g : Hom P Q) :
    (ι → B) →ₗ[B] Q.toExtension.Cotangent :=
  ∑ i, LinearMap.smulRight (LinearMap.proj i)
    (Cotangent.mk ⟨f.val i - g.val i, val_sub_mem_ker f g i⟩)

/-- The contraction attached to two parallel presentation morphisms evaluates
on a generator `dx_i` to the class of the difference of lifts. -/
theorem contraction_apply [Fintype ι] (f g : Hom P Q) (dx : ι → B) :
    contraction f g dx =
      ∑ i, dx i • Cotangent.mk ⟨f.val i - g.val i, val_sub_mem_ker f g i⟩ :=
  sorry

end Hom

end Presentation

variable {P : Presentation A B I ι} {Q : Presentation A B I ι'}
variable {T : Presentation A B I ι''}

/-- The degree-one component of the chain map induced by a morphism of presentations
commutes with the Jacobian differentials. -/
theorem chainMap_one_zero_comm [Fintype ι] [Fintype ι'] (f : Presentation.Hom P Q) :
    ModuleCat.ofHom (Cotangent.map f.toExtensionHom) ≫ (complex Q).d 1 0 =
      (complex P).d 1 0 ≫ ModuleCat.ofHom (Presentation.Hom.jacobianOnVars f) :=
  sorry

/-- Higher components of the induced chain map are zero, and the resulting
squares commute. -/
theorem chainMap_succ_comm [Fintype ι] [Fintype ι'] (f : Presentation.Hom P Q) (n : ℕ)
    (p :
      Σ' (zero : (complex P).X n ⟶ (complex Q).X n)
        (one : (complex P).X (n + 1) ⟶ (complex Q).X (n + 1)),
        one ≫ (complex Q).d (n + 1) n = (complex P).d (n + 1) n ≫ zero) :
    (0 : (complex P).X (n + 2) ⟶ (complex Q).X (n + 2)) ≫ (complex Q).d (n + 2) (n + 1) =
      (complex P).d (n + 2) (n + 1) ≫ p.2.1 :=
  sorry

/-- The map of completed naive cotangent complexes induced by a morphism of
presentations. -/
def chainMap [Fintype ι] [Fintype ι'] (f : Presentation.Hom P Q) :
    complex P ⟶ complex Q :=
  ChainComplex.mkHom _ _
    (ModuleCat.ofHom (Presentation.Hom.jacobianOnVars f))
    (ModuleCat.ofHom (Cotangent.map f.toExtensionHom))
    (chainMap_one_zero_comm f)
    (fun n p ↦ ⟨0, chainMap_succ_comm f n p⟩)

/-- The chain map induced by the identity presentation morphism is the identity. -/
theorem chainMap_id [Fintype ι] (P : Presentation A B I ι) :
    chainMap (Presentation.Hom.id P) = 𝟙 (complex P) :=
  sorry

/-- Induced chain maps respect composition of presentation morphisms. -/
theorem chainMap_comp [Fintype ι] [Fintype ι'] [Fintype ι'']
    (f : Presentation.Hom P Q) (g : Presentation.Hom Q T) :
    chainMap (g.comp f) = chainMap f ≫ chainMap g :=
  sorry

/-- The degree-zero component of an induced chain map is the Jacobian of the lifts. -/
theorem chainMap_f_zero [Fintype ι] [Fintype ι'] (f : Presentation.Hom P Q) :
    (chainMap f).f 0 = ModuleCat.ofHom (Presentation.Hom.jacobianOnVars f) :=
  sorry

/-- The degree-one component of an induced chain map is the induced conormal map. -/
theorem chainMap_f_one [Fintype ι] [Fintype ι'] (f : Presentation.Hom P Q) :
    (chainMap f).f 1 = ModuleCat.ofHom (Cotangent.map f.toExtensionHom) :=
  sorry

/-- Homotopy components comparing the chain maps of two parallel presentation
morphisms. The only possibly nonzero term is the contraction
`(ι → B) ⟶ Q.toExtension.Cotangent` in degrees `0 → 1`. -/
def homotopyHom [Fintype ι] [Fintype ι'] (f g : Presentation.Hom P Q) (i j : ℕ) :
    (complex P).X i ⟶ (complex Q).X j :=
  match i, j with
  | 0, 1 => ModuleCat.ofHom (Presentation.Hom.contraction f g)
  | _, _ => 0

/-- Homotopy components vanish unless they raise homological degree by one. -/
theorem homotopyHom_zero [Fintype ι] [Fintype ι'] (f g : Presentation.Hom P Q)
    (i j : ℕ) (hij : ¬(ComplexShape.down ℕ).Rel j i) :
    homotopyHom f g i j = 0 :=
  sorry

/-- The homotopy identity for the difference of two induced chain maps. -/
theorem homotopyHom_comm [Fintype ι] [Fintype ι'] (f g : Presentation.Hom P Q) (i : ℕ) :
    (chainMap f).f i =
      dNext i (homotopyHom f g) + prevD i (homotopyHom f g) + (chainMap g).f i :=
  sorry

/-- Any two chain maps induced by parallel morphisms of presentations are
chain-homotopic. -/
def chainMapHomotopy [Fintype ι] [Fintype ι'] (f g : Presentation.Hom P Q) :
    Homotopy (chainMap f) (chainMap g) where
  hom := homotopyHom f g
  zero := homotopyHom_zero f g
  comm := homotopyHom_comm f g

/-- The underlying family of the comparison homotopy is `homotopyHom`. -/
theorem chainMapHomotopy_hom [Fintype ι] [Fintype ι'] (f g : Presentation.Hom P Q) :
    (chainMapHomotopy f g).hom = homotopyHom f g :=
  sorry

/-- The forward and backward default presentation maps are homotopy inverse. -/
def homotopyEquiv [Fintype ι] [Fintype ι']
    (P : Presentation A B I ι) (Q : Presentation A B I ι') :
    HomotopyEquiv (complex P) (complex Q) where
  hom := chainMap (Presentation.defaultHom P Q)
  inv := chainMap (Presentation.defaultHom Q P)
  homotopyHomInvId :=
    (Homotopy.ofEq
        (chainMap_comp (Presentation.defaultHom P Q)
          (Presentation.defaultHom Q P)).symm).trans
      ((chainMapHomotopy
          ((Presentation.defaultHom Q P).comp (Presentation.defaultHom P Q))
          (Presentation.Hom.id P)).trans
        (Homotopy.ofEq (chainMap_id P)))
  homotopyInvHomId :=
    (Homotopy.ofEq
        (chainMap_comp (Presentation.defaultHom Q P)
          (Presentation.defaultHom P Q)).symm).trans
      ((chainMapHomotopy
          ((Presentation.defaultHom P Q).comp (Presentation.defaultHom Q P))
          (Presentation.Hom.id Q)).trans
        (Homotopy.ofEq (chainMap_id Q)))

/-- The forward map of the canonical homotopy equivalence is the chain map of
the default presentation morphism. -/
theorem homotopyEquiv_hom [Fintype ι] [Fintype ι']
    (P : Presentation A B I ι) (Q : Presentation A B I ι') :
    (homotopyEquiv P Q).hom = chainMap (Presentation.defaultHom P Q) :=
  sorry

end Algebra.NaiveCotangent.Adic
