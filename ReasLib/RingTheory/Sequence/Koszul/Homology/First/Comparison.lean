/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import ReasLib.RingTheory.Sequence.Koszul.Homology.First
public import ReasLib.RingTheory.Sequence.Koszul.Regularity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison with first homology of the full Koszul complex

The explicit low-degree model for first Koszul homology maps canonically to the `2, 1, 0`
truncation of the tensor Koszul complex.  Its middle and right components are the standard
degree-one and degree-zero exterior-power identifications, while its left component sends a
matrix of coefficients to the corresponding linear combination of elementary two-forms.

@stack 062E
-/

@[expose] public section

noncomputable section

universe u

namespace KoszulComplex.Homology.H1.Comparison

open CategoryTheory CategoryTheory.Limits ModuleCat
open scoped TensorProduct

variable {R : Type u} [CommRing R] {n : ℕ}
variable (f : Fin n → R) (N : Type u) [AddCommGroup N] [Module R N]

/-- The standard basis vector of `Fin n → R` used in the low-degree comparison. -/
@[stacks 062E "basis vector for the first Koszul homology comparison"]
abbrev basisVector (i : Fin n) : Fin n → R :=
  Pi.basisFun R (Fin n) i

/-- The elementary degree-two tensor associated to a pair of basis vectors. -/
@[stacks 062E "elementary degree-two Koszul tensor"]
def elementaryTwoTensor (ij : Fin n × Fin n) :
    N →ₗ[R] N ⊗[R] ⋀[R]^2 (Fin n → R) :=
  (TensorProduct.mk R N (⋀[R]^2 (Fin n → R))).flip
    (exteriorPower.leftWedgeOne (basisVector (R := R) ij.1)
      (basisVector (R := R) ij.2))

/-- The degree-two component of the comparison from the explicit low-degree model to the
tensor Koszul complex. -/
@[stacks 062E "degree-two map in the first Koszul homology comparison"]
def degreeTwoMap :
    (Fin n × Fin n → N) →ₗ[R] N ⊗[R] ⋀[R]^2 (Fin n → R) :=
  LinearMap.lsum R (fun _ : Fin n × Fin n ↦ N) R
    (elementaryTwoTensor (R := R) N)

/-- The degree-two comparison is surjective because elementary wedges span the second exterior
power of the finite free module. -/
theorem degreeTwoMap_surjective :
    Function.Surjective (degreeTwoMap (R := R) (n := n) N) := sorry

/-- The degree-two component is an epimorphism in `ModuleCat R`. -/
@[stacks 062E "epimorphism of the degree-two comparison", instance]
instance degreeTwoMap_epi :
    Epi (ModuleCat.ofHom (degreeTwoMap (R := R) (n := n) N)) := sorry

/-- The canonical identification of the degree-one tensor Koszul term with `Fin n → N`. -/
@[stacks 062E "degree-one identification in the first Koszul homology comparison"]
def degreeOneEquiv :
    N ⊗[R] ⋀[R]^1 (Fin n → R) ≃ₗ[R] Fin n → N :=
  (exteriorPower.oneEquiv R (Fin n → R)).lTensor N ≪≫ₗ
    TensorProduct.piScalarRight R R N (Fin n)

/-- The inverse degree-one identification, regarded as a morphism in `ModuleCat R`. -/
@[stacks 062E "degree-one map in the first Koszul homology comparison"]
abbrev degreeOneMap :
    ModuleCat.of R (Fin n → N) ⟶
      ModuleCat.of R (N ⊗[R] ⋀[R]^1 (Fin n → R)) :=
  (degreeOneEquiv (R := R) N).symm.toModuleIso.hom

/-- The canonical identification of the degree-zero tensor Koszul term with `N`. -/
@[stacks 062E "degree-zero identification in the first Koszul homology comparison"]
def degreeZeroEquiv :
    N ⊗[R] ⋀[R]^0 (Fin n → R) ≃ₗ[R] N :=
  (exteriorPower.zeroEquiv R (Fin n → R)).lTensor N ≪≫ₗ
    TensorProduct.rid R N

/-- The inverse degree-zero identification, regarded as a morphism in `ModuleCat R`. -/
@[stacks 062E "degree-zero map in the first Koszul homology comparison"]
abbrev degreeZeroMap :
    ModuleCat.of R N ⟶ ModuleCat.of R (N ⊗[R] ⋀[R]^0 (Fin n → R)) :=
  (degreeZeroEquiv (R := R) (n := n) N).symm.toModuleIso.hom

/-- The `2, 1, 0` truncation that computes degree-one homology of the tensor Koszul complex. -/
@[stacks 062E "three-term model for first Koszul homology"]
abbrev fullModel : ShortComplex (ModuleCat R) :=
  (RingTheory.Sequence.koszulComplexOnTensorLeft R N f).sc' 2 1 0

/-- The degree-two component intertwines the explicit relation boundary with the Koszul
differential under the degree-one identification. -/
theorem relationBoundary_naturality :
    ModuleCat.ofHom (degreeTwoMap (R := R) N) ≫
        (fullModel (R := R) f N).f =
      ModuleCat.ofHom (KoszulComplex.Homology.H1.relationBoundary f N) ≫
        degreeOneMap (R := R) N := sorry

/-- The degree-one identification intertwines the linear-combination map with the degree-one
Koszul differential. -/
theorem linearCombination_naturality :
    degreeOneMap (R := R) N ≫
        (fullModel (R := R) f N).g =
      ModuleCat.ofHom (KoszulComplex.Homology.H1.linearCombination f N) ≫
        degreeZeroMap (R := R) (n := n) N := sorry

/-- The canonical map from the explicit low-degree model to the `2, 1, 0` truncation of the
tensor Koszul complex. -/
@[stacks 062E "low-degree comparison for first Koszul homology"]
abbrev modelMap :
    KoszulComplex.Homology.H1.model f N ⟶
      fullModel (R := R) f N :=
  ShortComplex.homMk
    (ModuleCat.ofHom (degreeTwoMap (R := R) N))
    (degreeOneMap (R := R) N)
    (degreeZeroMap (R := R) (n := n) N)
    (relationBoundary_naturality (R := R) f N)
    (linearCombination_naturality (R := R) f N)

/-- The homology map of `modelMap` is an isomorphism by the epi-iso-mono criterion for morphisms
of short complexes. -/
@[stacks 062E "homology isomorphism of the low-degree model map", instance]
instance modelMap_homologyMap_isIso :
    IsIso (ShortComplex.homologyMap (modelMap (R := R) f N)) := sorry

/-- Degree-one homology of the full tensor Koszul complex is canonically identified with the
homology of its `2, 1, 0` truncation. -/
@[stacks 062E "full-to-truncated first Koszul homology isomorphism"]
def fullHomologyIso :
    (RingTheory.Sequence.koszulComplexOnTensorLeft R N f).homology 1 ≅
      (fullModel (R := R) f N).homology :=
  (RingTheory.Sequence.koszulComplexOnTensorLeft R N f).homologyIsoSc'
    2 1 0 (ChainComplex.prev ℕ 1) (ChainComplex.next_nat_succ 0)

/-- The canonical comparison from the explicit first-homology owner to degree-one homology of
the full tensor Koszul complex. -/
@[stacks 062E "explicit model computes first Koszul homology"]
noncomputable def comparison :
    KoszulComplex.Homology.H1.obj f N ⟶
      (RingTheory.Sequence.koszulComplexOnTensorLeft R N f).homology 1 :=
  ShortComplex.homologyMap (modelMap (R := R) f N) ≫
    (fullHomologyIso (R := R) f N).inv

/-- The canonical comparison with degree-one Koszul homology is an isomorphism. -/
@[stacks 062E "first Koszul homology comparison isomorphism", instance]
instance comparison_isIso :
    IsIso (comparison (R := R) f N) := sorry

#synth Epi (ModuleCat.ofHom (degreeTwoMap (R := R) (n := n) N))
#synth IsIso (degreeOneMap (R := R) (n := n) N)
#synth Mono (degreeZeroMap (R := R) (n := n) N)
#synth IsIso (ShortComplex.homologyMap (modelMap (R := R) f N))
#synth IsIso (comparison (R := R) f N)

end KoszulComplex.Homology.H1.Comparison

namespace KoszulComplex.Homology.H1

open CategoryTheory.Limits

variable {R : Type u} [CommRing R] {n : ℕ}
variable (f : Fin n → R) (N : Type u) [AddCommGroup N] [Module R N]

/-- Vanishing of the explicit low-degree model is equivalent to the canonical finite-family
`H₁`-regularity predicate. -/
@[stacks 062E "explicit first-homology model and H1-regularity"]
theorem isH1RegularOn_iff_isZero :
    RingTheory.Sequence.IsH1RegularOn N f ↔ IsZero (obj f N) := sorry

end KoszulComplex.Homology.H1
