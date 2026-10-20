module

public import ReasLib.Algebra.Homology.ChainGradedAlgebra.Quotient
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Augmentation
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Nonnegative
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.OfPredifferential
public import ReasLib.LinearAlgebra.QuotientByIdeal.Scalar
public import ReasLib.RingTheory.Algebra.Quotient.BaseIdeal

/-!
# Quotients of augmented chain differential graded algebras

This leaf lifts the degreewise quotient of a chain-graded algebra to chain DGAs and their
homomorphisms.  For an augmentation `A ⟶ S`, it also constructs the canonical augmentation
after quotienting the base by `I`, with target `S ⧸ I.map (algebraMap R S)`.
-/

@[expose] public section

noncomputable section

open CategoryTheory ComplexShape HomologicalComplex

universe u v

namespace ChainDGAlgebra

variable {R : Type u} [CommRing R]

namespace IdealQuotient

/-- The degree-`n` component of a chain DGA after quotienting by a base ideal. -/
abbrev Piece (A : ChainDGAlgebra.{u, v} R) (I : Ideal R) (n : ℤ) : Type v :=
  ChainGradedAlgebra.IdealQuotient.Piece A.toChainGradedAlgebra I n

end IdealQuotient

/-- The chain DGA over `R ⧸ I` obtained by quotienting every homogeneous component by the
multiples of `I`. -/
@[stacks 00DV "chain DGA modulo a base ideal"]
def quotientByIdeal (A : ChainDGAlgebra.{u, v} R) (I : Ideal R) :
    ChainDGAlgebra.{u, v} (R ⧸ I) :=
  ChainGradedAlgebra.Predifferential.toChainDGAlgebra
    (ChainGradedAlgebra.Predifferential.quotientByIdeal A.predifferential I)
    (ChainGradedAlgebra.Predifferential.isSquareZero_quotientByIdeal
      A.predifferential_isSquareZero I)

namespace IdealQuotient

/-- The quotient DGA has the degreewise quotient as its underlying chain-graded algebra. -/
@[simp]
theorem toChainGradedAlgebra (A : ChainDGAlgebra.{u, v} R) (I : Ideal R) :
    (A.quotientByIdeal I).toChainGradedAlgebra =
      A.toChainGradedAlgebra.quotientByIdeal I := sorry

/-- The quotient class of a homogeneous element, viewed in the quotient chain DGA. -/
def mk (A : ChainDGAlgebra.{u, v} R) (I : Ideal R) (n : ℤ) :
    A.X n → (A.quotientByIdeal I).X n :=
  ChainGradedAlgebra.IdealQuotient.mk A.toChainGradedAlgebra I n

/-- The quotient differential sends a representative to the class of its differential. -/
@[simp]
theorem d_mk (A : ChainDGAlgebra.{u, v} R) (I : Ideal R) (n : ℤ) (x : A.X n) :
    (A.quotientByIdeal I).d n (mk A I n x) =
      mk A I (n - 1) (A.d n x) := sorry

/-- Quotient multiplication sends representatives to the class of their product. -/
@[simp]
theorem mul_mk (A : ChainDGAlgebra.{u, v} R) (I : Ideal R) (n m : ℤ)
    (x : A.X n) (y : A.X m) :
    (A.quotientByIdeal I).mul n m (mk A I n x) (mk A I m y) =
      mk A I (n + m) (A.mul n m x y) := sorry

/-- The unit of the quotient DGA is the class of the original unit. -/
@[simp]
theorem one_eq_mk (A : ChainDGAlgebra.{u, v} R) (I : Ideal R) :
    (A.quotientByIdeal I).one = mk A I 0 A.one := sorry

/-- Strict commutativity descends canonically to the quotient by a base ideal. -/
@[stacks 00DV "strictly commutative chain DGA modulo a base ideal"]
instance isStrictlyCommutative (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative]
    (I : Ideal R) : (A.quotientByIdeal I).IsStrictlyCommutative := sorry

end IdealQuotient

namespace Hom

variable {A B C : ChainDGAlgebra.{u, v} R}

/-- The degree-`n` component of a chain-DGA homomorphism after quotienting by a base ideal. -/
def quotientComponent (f : Hom A B) (I : Ideal R) (n : ℤ) :
    (A.quotientByIdeal I).X n →ₗ[R ⧸ I] (B.quotientByIdeal I).X n :=
  LinearMap.IdealQuotient.map (f.toChainMap.f n).hom I

/-- A quotient component sends the class of a representative to the class of its image. -/
@[simp]
theorem quotientComponent_mk (f : Hom A B) (I : Ideal R) (n : ℤ) (x : A.X n) :
    quotientComponent f I n (IdealQuotient.mk A I n x) =
      IdealQuotient.mk B I n (f n x) := sorry

/-- The quotient component maps commute with the quotient differentials. -/
theorem quotientComponent_comm (f : Hom A B) (I : Ideal R) (n m : ℤ)
    (hnm : (down ℤ).Rel n m) :
    ModuleCat.ofHom (quotientComponent f I n) ≫ (B.quotientByIdeal I).toChainComplex.d n m =
      (A.quotientByIdeal I).toChainComplex.d n m ≫
        ModuleCat.ofHom (quotientComponent f I m) := sorry

/-- The chain map induced by a chain-DGA homomorphism on degreewise base-ideal quotients. -/
def quotientChainMap (f : Hom A B) (I : Ideal R) :
    (A.quotientByIdeal I).toChainComplex ⟶
      (B.quotientByIdeal I).toChainComplex where
  f n := ModuleCat.ofHom (quotientComponent f I n)
  comm' := quotientComponent_comm f I

/-- The quotient chain map preserves the quotient unit. -/
theorem quotientChainMap_map_one (f : Hom A B) (I : Ideal R) :
    (quotientChainMap f I).f 0 (A.quotientByIdeal I).one =
      (B.quotientByIdeal I).one := sorry

/-- The quotient chain map preserves quotient multiplication. -/
theorem quotientChainMap_map_mul (f : Hom A B) (I : Ideal R) (n m : ℤ)
    (x : (A.quotientByIdeal I).X n) (y : (A.quotientByIdeal I).X m) :
    (quotientChainMap f I).f (n + m) ((A.quotientByIdeal I).mul n m x y) =
      (B.quotientByIdeal I).mul n m
        ((quotientChainMap f I).f n x) ((quotientChainMap f I).f m y) := sorry

/-- A chain-DGA homomorphism descends canonically through the degreewise quotient by a base
ideal. -/
@[stacks 00DV "chain-DGA homomorphisms modulo a base ideal"]
def quotientByIdeal (f : Hom A B) (I : Ideal R) :
    Hom (A.quotientByIdeal I) (B.quotientByIdeal I) where
  toChainMap := quotientChainMap f I
  map_one := quotientChainMap_map_one f I
  map_mul := quotientChainMap_map_mul f I

/-- The quotient homomorphism sends a homogeneous representative to the class of its image. -/
@[simp]
theorem quotientByIdeal_mk (f : Hom A B) (I : Ideal R) (n : ℤ) (x : A.X n) :
    f.quotientByIdeal I n (IdealQuotient.mk A I n x) =
      IdealQuotient.mk B I n (f n x) := sorry

/-- Quotienting the identity homomorphism gives the identity of the quotient DGA. -/
@[simp]
theorem quotientByIdeal_id (A : ChainDGAlgebra.{u, v} R) (I : Ideal R) :
    (id A).quotientByIdeal I = id (A.quotientByIdeal I) := sorry

/-- Quotienting a composite is the composite of the quotient homomorphisms. -/
@[simp]
theorem quotientByIdeal_comp (g : Hom B C) (f : Hom A B) (I : Ideal R) :
    (comp g f).quotientByIdeal I =
      comp (g.quotientByIdeal I) (f.quotientByIdeal I) := sorry

/-- The linear map on degree-`n` homology induced by a quotient homomorphism. -/
def quotientHomologyMap (f : Hom A B) (I : Ideal R) (n : ℤ) :
    (A.quotientByIdeal I).homology n →ₗ[R ⧸ I]
      (B.quotientByIdeal I).homology n :=
  (f.quotientByIdeal I).homologyLinearMap n

/-- The induced quotient homology map sends a cycle class to the class of its mapped cycle. -/
@[simp]
theorem quotientHomologyMap_homologyπ (f : Hom A B) (I : Ideal R) (n : ℤ)
    (x : (A.quotientByIdeal I).cycles n) :
    f.quotientHomologyMap I n ((A.quotientByIdeal I).homologyπ n x) =
      (B.quotientByIdeal I).homologyπ n
        (HomologicalComplex.cyclesMap (f.quotientByIdeal I).toChainMap n x) := sorry

end Hom

namespace IdealQuotient

variable {A : ChainDGAlgebra.{u, v} R}
variable {S : Type v} [CommRing S] [Algebra R S]

/-- The degree-zero representative map of an augmentation, followed by the quotient map onto
`S ⧸ I.map (algebraMap R S)`. -/
def augmentationRepresentativeMap (augmentation : Augmentation A S) (I : Ideal R) :
    A.X 0 →ₗ[R] S ⧸ I.map (algebraMap R S) :=
  (Ideal.Quotient.mkₐ R (I.map (algebraMap R S))).toLinearMap.comp
    (augmentation.toChainMap.f 0 ≫ (degreeZeroIso R S).hom).hom

/-- Multiples of the base ideal lie in the kernel of the representative augmentation map. -/
theorem smulTop_le_ker_augmentationRepresentativeMap
    (augmentation : Augmentation A S) (I : Ideal R) :
    I • (⊤ : Submodule R (A.X 0)) ≤
      LinearMap.ker (augmentationRepresentativeMap augmentation I) := sorry

/-- The `R`-linear descent of the representative augmentation map to the quotient piece. -/
def augmentationLift (augmentation : Augmentation A S) (I : Ideal R) :
    Piece A I 0 →ₗ[R] S ⧸ I.map (algebraMap R S) :=
  (I • (⊤ : Submodule R (A.X 0))).liftQ
    (augmentationRepresentativeMap augmentation I)
    (smulTop_le_ker_augmentationRepresentativeMap augmentation I)

/-- The descended augmentation map respects the canonical quotient-ring scalar action. -/
theorem augmentationLift_map_smul (augmentation : Augmentation A S) (I : Ideal R)
    (r : R ⧸ I) (x : Piece A I 0) :
    augmentationLift augmentation I (r • x) =
      r • augmentationLift augmentation I x := sorry

/-- The quotient-linear degree-zero map associated to an augmentation. -/
def augmentationDegreeZeroMap (augmentation : Augmentation A S) (I : Ideal R) :
    Piece A I 0 →ₗ[R ⧸ I] S ⧸ I.map (algebraMap R S) where
  toFun := augmentationLift augmentation I
  map_add' := (augmentationLift augmentation I).map_add
  map_smul' := augmentationLift_map_smul augmentation I

/-- The quotient-linear degree-zero augmentation sends a class to the class of its original
augmentation value. -/
@[simp]
theorem augmentationDegreeZeroMap_mk (augmentation : Augmentation A S) (I : Ideal R)
    (x : A.X 0) :
    augmentationDegreeZeroMap augmentation I (mk A I 0 x) =
      Ideal.Quotient.mk (I.map (algebraMap R S))
        ((degreeZeroIso R S).hom (augmentation.toChainMap.f 0 x)) := sorry

/-- The quotient degree-zero augmentation annihilates every differential entering degree zero. -/
theorem augmentationDegreeZeroMap_d (augmentation : Augmentation A S) (I : Ideal R)
    (n : ℤ) (hn : (down ℤ).Rel n 0) :
    (A.quotientByIdeal I).toChainComplex.d n 0 ≫
        ModuleCat.ofHom (augmentationDegreeZeroMap augmentation I) = 0 := sorry

/-- The chain map from the quotient DGA to the mapped-ideal quotient of the augmentation
target. -/
def augmentationChainMap (augmentation : Augmentation A S) (I : Ideal R) :
    (A.quotientByIdeal I).toChainComplex ⟶
      degreeZeroComplex (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  HomologicalComplex.mkHomToSingle
    (K := (A.quotientByIdeal I).toChainComplex) (j := (0 : ℤ))
    (ModuleCat.ofHom (augmentationDegreeZeroMap augmentation I))
    (augmentationDegreeZeroMap_d augmentation I)

/-- On a degree-zero representative, the quotient chain map is the residue class of the
original augmentation value. -/
@[simp]
theorem augmentationChainMap_mk (augmentation : Augmentation A S) (I : Ideal R)
    (x : A.X 0) :
    (degreeZeroIso (R ⧸ I) (S ⧸ I.map (algebraMap R S))).hom
        ((augmentationChainMap augmentation I).f 0 (mk A I 0 x)) =
      Ideal.Quotient.mk (I.map (algebraMap R S))
        ((degreeZeroIso R S).hom (augmentation.toChainMap.f 0 x)) := sorry

/-- The quotient augmentation chain map preserves the unit in degree zero. -/
theorem augmentationChainMap_map_one (augmentation : Augmentation A S) (I : Ideal R) :
    (degreeZeroIso (R ⧸ I) (S ⧸ I.map (algebraMap R S))).hom
        ((augmentationChainMap augmentation I).f 0 (A.quotientByIdeal I).one) = 1 := sorry

/-- The quotient augmentation chain map preserves multiplication in degree zero. -/
theorem augmentationChainMap_map_mul (augmentation : Augmentation A S) (I : Ideal R)
    (x y : (A.quotientByIdeal I).X 0) :
    (degreeZeroIso (R ⧸ I) (S ⧸ I.map (algebraMap R S))).hom
        ((augmentationChainMap augmentation I).f 0
          ((A.quotientByIdeal I).mul 0 0 x y)) =
      (degreeZeroIso (R ⧸ I) (S ⧸ I.map (algebraMap R S))).hom
          ((augmentationChainMap augmentation I).f 0 x) *
        (degreeZeroIso (R ⧸ I) (S ⧸ I.map (algebraMap R S))).hom
          ((augmentationChainMap augmentation I).f 0 y) := sorry

end IdealQuotient

namespace Augmentation

variable {A : ChainDGAlgebra.{u, v} R}
variable {S : Type v} [CommRing S] [Algebra R S]

/-- The augmentation induced after quotienting the base by `I`, with target the quotient by the
extended ideal `I S`. -/
@[stacks 09PN "augmentation modulo a base ideal"]
def quotientByIdeal (augmentation : Augmentation A S) (I : Ideal R) :
    Augmentation (A.quotientByIdeal I) (S ⧸ I.map (algebraMap R S)) where
  toChainMap := IdealQuotient.augmentationChainMap augmentation I
  map_one := IdealQuotient.augmentationChainMap_map_one augmentation I
  map_mul := IdealQuotient.augmentationChainMap_map_mul augmentation I

/-- On a degree-zero representative, the quotient augmentation is the residue class of the
original augmentation value. -/
@[simp]
theorem quotientByIdeal_mk (augmentation : Augmentation A S) (I : Ideal R) (x : A.X 0) :
    (degreeZeroIso (R ⧸ I) (S ⧸ I.map (algebraMap R S))).hom
        ((augmentation.quotientByIdeal I).toChainMap.f 0
          (IdealQuotient.mk A I 0 x)) =
      Ideal.Quotient.mk (I.map (algebraMap R S))
        ((degreeZeroIso R S).hom (augmentation.toChainMap.f 0 x)) := sorry

variable [A.IsStrictlyCommutative]

/-- The algebra homomorphism on zeroth homology induced by the quotient augmentation. -/
@[stacks 09PN "zeroth-homology augmentation modulo a base ideal"]
def quotientHomologyZeroMap (augmentation : Augmentation A S) (I : Ideal R) :
    (A.quotientByIdeal I).homologyZero →ₐ[R ⧸ I]
      S ⧸ I.map (algebraMap R S) :=
  (augmentation.quotientByIdeal I).homologyZeroMap

/-- The quotient homology augmentation is computed on cycle classes by the degree-zero
quotient chain map. -/
@[simp]
theorem quotientHomologyZeroMap_homologyπ (augmentation : Augmentation A S) (I : Ideal R)
    (x : (A.quotientByIdeal I).cycles 0) :
    augmentation.quotientHomologyZeroMap I
        ((A.quotientByIdeal I).homologyπ 0 x) =
      (degreeZeroIso (R ⧸ I) (S ⧸ I.map (algebraMap R S))).hom
        ((augmentation.quotientByIdeal I).toChainMap.f 0
          ((A.quotientByIdeal I).iCycles 0 x)) := sorry

/-- For a nonnegative DGA whose augmentation identifies zeroth homology with `S`, quotienting by
a base ideal identifies zeroth homology with the corresponding quotient of `S`. -/
theorem quotientHomologyZeroMap_bijective (augmentation : Augmentation A S)
    [A.IsNonnegative]
    (hH0 : Function.Bijective augmentation.homologyZeroMap) (I : Ideal R) :
    Function.Bijective (augmentation.quotientHomologyZeroMap I) := sorry

end Augmentation

end ChainDGAlgebra

/- The scalar tower for each quotient homogeneous component is supplied by the neutral quotient
module owner, rather than by a DGA-specific instance. -/
