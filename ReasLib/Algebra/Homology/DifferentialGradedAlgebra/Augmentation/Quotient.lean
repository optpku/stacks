/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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

namespace HomologicalComplex

variable {R : Type u} [CommRing R]

/-- The canonical map from degree-zero elements to their homology classes when the outgoing
differential vanishes.  The lift uses the existing cycles object. -/
noncomputable def degreeZeroClassMap (K : ChainComplex (ModuleCat.{v} R) ℤ)
    (hd : K.d 0 (-1) = 0) : K.X 0 →ₗ[R] K.homology 0 :=
  (K.liftCycles (𝟙 _) (-1) (by apply (ComplexShape.down ℤ).next_eq'; decide)
    (by simp [hd]) ≫ K.homologyπ 0).hom

/-- On a bundled cycle, the degree-zero class map is the canonical homology projection. -/
theorem degreeZeroClassMap_iCycles (K : ChainComplex (ModuleCat.{v} R) ℤ)
    (hd : K.d 0 (-1) = 0) (x : K.cycles 0) :
    degreeZeroClassMap K hd (K.iCycles 0 x) = K.homologyπ 0 x := by
  have h : K.iCycles 0 ≫ K.liftCycles (𝟙 _) (-1)
      (by apply (ComplexShape.down ℤ).next_eq'; decide) (by simp [hd]) = 𝟙 _ := by
    rw [← cancel_mono (K.iCycles 0)]
    simp
  exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f ≫ K.homologyπ 0) h) x

/-- Every degree-zero homology class has a degree-zero representative. -/
theorem degreeZeroClassMap_surjective (K : ChainComplex (ModuleCat.{v} R) ℤ)
    (hd : K.d 0 (-1) = 0) : Function.Surjective (degreeZeroClassMap K hd) := by
  intro x
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ 0)).mp inferInstance x
  exact ⟨K.iCycles 0 x, degreeZeroClassMap_iCycles K hd x⟩

/-- A degree-zero cycle represents zero precisely when it is an incoming boundary. -/
theorem homologyπ_zero_iff_boundary (K : ChainComplex (ModuleCat.{v} R) ℤ)
    (x : K.cycles 0) :
    K.homologyπ 0 x = 0 ↔ ∃ y : K.X 1, K.d 1 0 y = K.iCycles 0 x := by
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (K.toCycles 1 0) (K.homologyπ 0) (K.toCycles_comp_homologyπ 1 0)
  have hS : S.Exact := S.exact_of_g_is_cokernel
    (K.homologyIsCokernel 1 0 (by apply (ComplexShape.down ℤ).prev_eq'; decide))
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := S.moduleCat_exact_iff.mp hS x hx
    refine ⟨y, ?_⟩
    have h := congrArg (fun z ↦ K.iCycles 0 z) hy
    exact (ConcreteCategory.congr_hom (K.toCycles_i 1 0) y).symm.trans h
  · rintro ⟨y, hy⟩
    have hi : K.toCycles 1 0 y = x := by
      apply (ModuleCat.mono_iff_injective (K.iCycles 0)).mp inferInstance
      exact (ConcreteCategory.congr_hom (K.toCycles_i 1 0) y).trans hy
    rw [← hi]
    exact ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ 1 0) y

/-- The degree-zero class of an element vanishes precisely when it is a boundary. -/
theorem degreeZeroClassMap_zero_iff (K : ChainComplex (ModuleCat.{v} R) ℤ)
    (hd : K.d 0 (-1) = 0) (x : K.X 0) :
    K.degreeZeroClassMap hd x = 0 ↔ ∃ y : K.X 1, K.d 1 0 y = x := by
  change K.homologyπ 0
    (K.liftCycles (𝟙 _) (-1) (by apply (ComplexShape.down ℤ).next_eq'; decide)
      (by simp [hd]) x) = 0 ↔ _
  rw [homologyπ_zero_iff_boundary]
  have hi := ConcreteCategory.congr_hom
    (K.liftCycles_i (𝟙 _) (-1)
      (by apply (ComplexShape.down ℤ).next_eq'; decide) (by simp [hd])) x
  change K.iCycles 0 _ = x at hi
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, hy.trans hi⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, hy.trans hi.symm⟩

/-- Every incoming differential has zero degree-zero class. -/
theorem degreeZeroClassMap_boundary (K : ChainComplex (ModuleCat.{v} R) ℤ)
    (hd : K.d 0 (-1) = 0) (y : K.X 1) :
    K.degreeZeroClassMap hd (K.d 1 0 y) = 0 :=
  (K.degreeZeroClassMap_zero_iff hd _).mpr ⟨y, rfl⟩

/-- The class map identifies exactly the representatives differing by a boundary. -/
theorem degreeZeroClassMap_eq_iff (K : ChainComplex (ModuleCat.{v} R) ℤ)
    (hd : K.d 0 (-1) = 0) (x y : K.X 0) :
    K.degreeZeroClassMap hd x = K.degreeZeroClassMap hd y ↔
      ∃ z : K.X 1, K.d 1 0 z = x - y := by
  rw [← sub_eq_zero, ← map_sub, degreeZeroClassMap_zero_iff]

/-- The class map commutes with the canonical homology map of a chain map. -/
theorem degreeZeroClassMap_naturality
    {K L : ChainComplex (ModuleCat.{v} R) ℤ}
    (hK : K.d 0 (-1) = 0) (hL : L.d 0 (-1) = 0) (f : K ⟶ L) (x : K.X 0) :
    homologyMap f 0 (K.degreeZeroClassMap hK x) =
      L.degreeZeroClassMap hL (f.f 0 x) := by
  let a : K.X 0 ⟶ K.cycles 0 := K.liftCycles (𝟙 _) (-1)
    (by apply (ComplexShape.down ℤ).next_eq'; decide) (by simp [hK])
  let b : L.X 0 ⟶ L.cycles 0 := L.liftCycles (𝟙 _) (-1)
    (by apply (ComplexShape.down ℤ).next_eq'; decide) (by simp [hL])
  have hab : a ≫ cyclesMap f 0 = f.f 0 ≫ b := by
    rw [← cancel_mono (L.iCycles 0)]
    simp [a, b, Category.assoc]
  change homologyMap f 0 (K.homologyπ 0 (a x)) = L.homologyπ 0 (b (f.f 0 x))
  exact (ConcreteCategory.congr_hom (homologyπ_naturality f 0) (a x)).trans
    (congrArg (L.homologyπ 0) (ConcreteCategory.congr_hom hab x))

end HomologicalComplex

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
      A.toChainGradedAlgebra.quotientByIdeal I := rfl

/-- The quotient class of a homogeneous element, viewed in the quotient chain DGA. -/
def mk (A : ChainDGAlgebra.{u, v} R) (I : Ideal R) (n : ℤ) :
    A.X n → (A.quotientByIdeal I).X n :=
  ChainGradedAlgebra.IdealQuotient.mk A.toChainGradedAlgebra I n

/-- The quotient class used by the DGA is the canonical submodule quotient class. -/
theorem mk_eq_quotient_mk (A : ChainDGAlgebra.{u, v} R) (I : Ideal R) (n : ℤ)
    (x : A.X n) :
    mk A I n x = Submodule.Quotient.mk x :=
  Ideal.Quotient.tensorModuleEquiv_one_tmul I (A.X n) x

/-- Every element of a quotient homogeneous piece has a representative. -/
theorem mk_surjective (A : ChainDGAlgebra.{u, v} R) (I : Ideal R) (n : ℤ) :
    Function.Surjective (mk A I n) := by
  intro x
  obtain ⟨x, rfl⟩ := (I • (⊤ : Submodule R (A.X n))).mkQ_surjective x
  exact ⟨x, mk_eq_quotient_mk A I n x⟩

/-- The quotient differential sends a representative to the class of its differential. -/
@[simp]
theorem d_mk (A : ChainDGAlgebra.{u, v} R) (I : Ideal R) (n : ℤ) (x : A.X n) :
    (A.quotientByIdeal I).d n (mk A I n x) =
      mk A I (n - 1) (A.d n x) := by
  change (ChainGradedAlgebra.Predifferential.toChainDGAlgebra _ _).d n _ = _
  rw [ChainGradedAlgebra.Predifferential.toChainDGAlgebra_d_apply]
  exact ChainGradedAlgebra.Derivation.quotientByIdeal_mk A.predifferential I n x

/-- Quotient multiplication sends representatives to the class of their product. -/
@[simp]
theorem mul_mk (A : ChainDGAlgebra.{u, v} R) (I : Ideal R) (n m : ℤ)
    (x : A.X n) (y : A.X m) :
    (A.quotientByIdeal I).mul n m (mk A I n x) (mk A I m y) =
      mk A I (n + m) (A.mul n m x y) :=
  ChainGradedAlgebra.IdealQuotient.mul_mk A.toChainGradedAlgebra I n m x y

/-- The unit of the quotient DGA is the class of the original unit. -/
@[simp]
theorem one_eq_mk (A : ChainDGAlgebra.{u, v} R) (I : Ideal R) :
    (A.quotientByIdeal I).one = mk A I 0 A.one := rfl

/-- Strict commutativity descends canonically to the quotient by a base ideal. -/
@[stacks 00DV "strictly commutative chain DGA modulo a base ideal"]
instance isStrictlyCommutative (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative]
    (I : Ideal R) : (A.quotientByIdeal I).IsStrictlyCommutative where
  mul_comm {n m} x y := by
    obtain ⟨x, rfl⟩ := mk_surjective A I n x
    obtain ⟨y, rfl⟩ := mk_surjective A I m y
    have hcast {i j : ℤ} (h : i = j) (z : A.X i) :
        mk A I j (cast (congrArg (fun k : ℤ ↦ (A.X k : Type v)) h) z) =
          cast (congrArg (fun k : ℤ ↦ ((A.quotientByIdeal I).X k : Type v)) h)
            (mk A I i z) := by
      subst j
      rfl
    have hsmul (i : ℤ) (r : R) (z : A.X i) :
        mk A I i (r • z) = algebraMap R (R ⧸ I) r • mk A I i z := by
      exact ((ChainGradedAlgebra.IdealQuotient.mk A.toChainGradedAlgebra I i).map_smul r z).trans
        (IsScalarTower.algebraMap_smul (R ⧸ I) r
          (ChainGradedAlgebra.IdealQuotient.mk A.toChainGradedAlgebra I i z)).symm
    rw [mul_mk, mul_mk]
    calc
      _ = mk A I (n + m)
          (cast (congrArg (fun k : ℤ ↦ (A.X k : Type v)) (add_comm m n))
            (((n * m).negOnePow : R) • A.mul m n y x)) :=
        congrArg (mk A I (n + m)) (IsCommutative.mul_comm x y)
      _ = _ := by
        rw [hcast (add_comm m n), hsmul]
        simp only [map_intCast]
  sq_eq_zero_of_odd {n} hn x := by
    obtain ⟨x, rfl⟩ := mk_surjective A I n x
    rw [mul_mk]
    calc
      _ = mk A I (n + n) 0 := congrArg (mk A I (n + n))
        (IsStrictlyCommutative.sq_eq_zero_of_odd hn x)
      _ = 0 := by
        rw [mk_eq_quotient_mk]
        rfl

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
      IdealQuotient.mk B I n (f n x) := by
  rw [IdealQuotient.mk_eq_quotient_mk, IdealQuotient.mk_eq_quotient_mk]
  exact LinearMap.IdealQuotient.map_mk (f.toChainMap.f n).hom I x

/-- The quotient component maps commute with the quotient differentials. -/
theorem quotientComponent_comm (f : Hom A B) (I : Ideal R) (n m : ℤ)
    (hnm : (down ℤ).Rel n m) :
    ModuleCat.ofHom (quotientComponent f I n) ≫ (B.quotientByIdeal I).toChainComplex.d n m =
      (A.quotientByIdeal I).toChainComplex.d n m ≫
        ModuleCat.ofHom (quotientComponent f I m) := by
  have hm : m = n - 1 := by
    change m + 1 = n at hnm
    omega
  subst m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := IdealQuotient.mk_surjective A I n x
  change (B.quotientByIdeal I).d n (quotientComponent f I n (IdealQuotient.mk A I n x)) =
    quotientComponent f I (n - 1) ((A.quotientByIdeal I).d n (IdealQuotient.mk A I n x))
  rw [quotientComponent_mk, IdealQuotient.d_mk, IdealQuotient.d_mk, quotientComponent_mk]
  exact congrArg (IdealQuotient.mk B I (n - 1))
    (ConcreteCategory.congr_hom (f.toChainMap.comm n (n - 1)) x)

/-- The chain map induced by a chain-DGA homomorphism on degreewise base-ideal quotients. -/
def quotientChainMap (f : Hom A B) (I : Ideal R) :
    (A.quotientByIdeal I).toChainComplex ⟶
      (B.quotientByIdeal I).toChainComplex where
  f n := ModuleCat.ofHom (quotientComponent f I n)
  comm' := quotientComponent_comm f I

/-- The quotient chain map preserves the quotient unit. -/
theorem quotientChainMap_map_one (f : Hom A B) (I : Ideal R) :
    (quotientChainMap f I).f 0 (A.quotientByIdeal I).one =
      (B.quotientByIdeal I).one := by
  change quotientComponent f I 0 (A.quotientByIdeal I).one = _
  rw [IdealQuotient.one_eq_mk, quotientComponent_mk]
  exact (congrArg (IdealQuotient.mk B I 0) f.map_one).trans
    (IdealQuotient.one_eq_mk B I).symm

/-- The quotient chain map preserves quotient multiplication. -/
theorem quotientChainMap_map_mul (f : Hom A B) (I : Ideal R) (n m : ℤ)
    (x : (A.quotientByIdeal I).X n) (y : (A.quotientByIdeal I).X m) :
    (quotientChainMap f I).f (n + m) ((A.quotientByIdeal I).mul n m x y) =
      (B.quotientByIdeal I).mul n m
        ((quotientChainMap f I).f n x) ((quotientChainMap f I).f m y) := by
  change quotientComponent f I (n + m) ((A.quotientByIdeal I).mul n m x y) =
    (B.quotientByIdeal I).mul n m (quotientComponent f I n x) (quotientComponent f I m y)
  obtain ⟨x, rfl⟩ := IdealQuotient.mk_surjective A I n x
  obtain ⟨y, rfl⟩ := IdealQuotient.mk_surjective A I m y
  rw [IdealQuotient.mul_mk, quotientComponent_mk, quotientComponent_mk,
    quotientComponent_mk, IdealQuotient.mul_mk]
  exact congrArg (IdealQuotient.mk B I (n + m)) (f.map_mul n m x y)

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
      IdealQuotient.mk B I n (f n x) :=
  quotientComponent_mk f I n x

/-- Quotienting the identity homomorphism gives the identity of the quotient DGA. -/
@[simp]
theorem quotientByIdeal_id (A : ChainDGAlgebra.{u, v} R) (I : Ideal R) :
    (id A).quotientByIdeal I = id (A.quotientByIdeal I) := by
  apply ext_toChainMap
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := IdealQuotient.mk_surjective A I n x
  exact quotientByIdeal_mk (id A) I n x

/-- Quotienting a composite is the composite of the quotient homomorphisms. -/
@[simp]
theorem quotientByIdeal_comp (g : Hom B C) (f : Hom A B) (I : Ideal R) :
    (comp g f).quotientByIdeal I =
      comp (g.quotientByIdeal I) (f.quotientByIdeal I) := by
  apply ext_toChainMap
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := IdealQuotient.mk_surjective A I n x
  change (comp g f).quotientByIdeal I n (IdealQuotient.mk A I n x) =
    g.quotientByIdeal I n (f.quotientByIdeal I n (IdealQuotient.mk A I n x))
  rw [quotientByIdeal_mk, quotientByIdeal_mk, quotientByIdeal_mk]
  rfl

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
        (HomologicalComplex.cyclesMap (f.quotientByIdeal I).toChainMap n x) :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (f.quotientByIdeal I).toChainMap n) x

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
      LinearMap.ker (augmentationRepresentativeMap augmentation I) := by
  apply Submodule.smul_le.mpr
  intro r hr x _
  change augmentationRepresentativeMap augmentation I (r • x) = 0
  rw [(augmentationRepresentativeMap augmentation I).map_smul]
  have hr0 : algebraMap R (S ⧸ I.map (algebraMap R S)) r = 0 := by
    change Ideal.Quotient.mk (I.map (algebraMap R S)) (algebraMap R S r) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
  rw [Algebra.smul_def, hr0, zero_mul]

/-- The `R`-linear descent of the representative augmentation map to the quotient piece. -/
def augmentationLift (augmentation : Augmentation A S) (I : Ideal R) :
    Piece A I 0 →ₗ[R] S ⧸ I.map (algebraMap R S) :=
  (I • (⊤ : Submodule R (A.X 0))).liftQ
    (augmentationRepresentativeMap augmentation I)
    (smulTop_le_ker_augmentationRepresentativeMap augmentation I)

/-- The original quotient descent agrees with the canonical quotient of the degree-zero
linear map followed by the mapped-ideal comparison. -/
theorem augmentationLift_eq_quotientMap (augmentation : Augmentation A S) (I : Ideal R) :
    augmentationLift augmentation I =
      (Ideal.Quotient.Map.idealQuotientEquiv (R := R) (S := S) I).toLinearMap.comp
        ((augmentation.toChainMap.f 0 ≫ (degreeZeroIso R S).hom).hom.quotientMapByIdeal I) := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on _ x ?_
  intro x
  exact (Ideal.Quotient.Map.idealQuotientEquiv_apply_mk I
    ((degreeZeroIso R S).hom (augmentation.toChainMap.f 0 x))).symm

/-- The descended augmentation map respects the canonical quotient-ring scalar action. -/
theorem augmentationLift_map_smul (augmentation : Augmentation A S) (I : Ideal R)
    (r : R ⧸ I) (x : Piece A I 0) :
    augmentationLift augmentation I (r • x) =
      r • augmentationLift augmentation I x :=
  (augmentationLift augmentation I).map_smul_of_quotient r x

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
        ((degreeZeroIso R S).hom (augmentation.toChainMap.f 0 x)) := by
  rw [mk_eq_quotient_mk]
  rfl

/-- The quotient degree-zero augmentation annihilates every differential entering degree zero. -/
theorem augmentationDegreeZeroMap_d (augmentation : Augmentation A S) (I : Ideal R)
    (n : ℤ) (hn : (down ℤ).Rel n 0) :
    (A.quotientByIdeal I).toChainComplex.d n 0 ≫
        ModuleCat.ofHom (augmentationDegreeZeroMap augmentation I) = 0 := by
  have hn1 : n = 1 := by
    change (0 : ℤ) + 1 = n at hn
    omega
  subst n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := mk_surjective A I 1 x
  change augmentationDegreeZeroMap augmentation I
    ((A.quotientByIdeal I).d 1 (mk A I 1 x)) = 0
  have hd : A.toChainComplex.d 1 0 ≫ augmentation.toChainMap.f 0 = 0 := by
    calc
      _ = augmentation.toChainMap.f 1 ≫ (degreeZeroComplex R S).d 1 0 :=
        (augmentation.toChainMap.comm 1 0).symm
      _ = 0 := by simp
  have hx : augmentation.toChainMap.f 0 (A.d 1 x) = 0 :=
    ConcreteCategory.congr_hom hd x
  calc
    _ = augmentationDegreeZeroMap augmentation I (mk A I 0 (A.d 1 x)) :=
      congrArg (augmentationDegreeZeroMap augmentation I) (d_mk A I 1 x)
    _ = Ideal.Quotient.mk (I.map (algebraMap R S))
        ((degreeZeroIso R S).hom (augmentation.toChainMap.f 0 (A.d 1 x))) :=
      augmentationDegreeZeroMap_mk augmentation I (A.d 1 x)
    _ = 0 := by rw [hx, map_zero, map_zero]

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
        ((degreeZeroIso R S).hom (augmentation.toChainMap.f 0 x)) := by
  unfold augmentationChainMap
  rw [HomologicalComplex.mkHomToSingle_f]
  change (degreeZeroIso (R ⧸ I) (S ⧸ I.map (algebraMap R S))).hom
    ((degreeZeroIso (R ⧸ I) (S ⧸ I.map (algebraMap R S))).inv
      (augmentationDegreeZeroMap augmentation I (mk A I 0 x))) = _
  rw [Iso.inv_hom_id_apply, augmentationDegreeZeroMap_mk]

/-- The quotient augmentation chain map preserves the unit in degree zero. -/
theorem augmentationChainMap_map_one (augmentation : Augmentation A S) (I : Ideal R) :
    (degreeZeroIso (R ⧸ I) (S ⧸ I.map (algebraMap R S))).hom
        ((augmentationChainMap augmentation I).f 0 (A.quotientByIdeal I).one) = 1 := by
  rw [one_eq_mk, augmentationChainMap_mk, augmentation.map_one, map_one]

/-- The quotient augmentation chain map preserves multiplication in degree zero. -/
theorem augmentationChainMap_map_mul (augmentation : Augmentation A S) (I : Ideal R)
    (x y : (A.quotientByIdeal I).X 0) :
    (degreeZeroIso (R ⧸ I) (S ⧸ I.map (algebraMap R S))).hom
        ((augmentationChainMap augmentation I).f 0
          ((A.quotientByIdeal I).mul 0 0 x y)) =
      (degreeZeroIso (R ⧸ I) (S ⧸ I.map (algebraMap R S))).hom
          ((augmentationChainMap augmentation I).f 0 x) *
        (degreeZeroIso (R ⧸ I) (S ⧸ I.map (algebraMap R S))).hom
          ((augmentationChainMap augmentation I).f 0 y) := by
  obtain ⟨x, rfl⟩ := mk_surjective A I 0 x
  obtain ⟨y, rfl⟩ := mk_surjective A I 0 y
  rw [mul_mk]
  calc
    _ = Ideal.Quotient.mk (I.map (algebraMap R S))
        ((degreeZeroIso R S).hom (augmentation.toChainMap.f 0 (A.mul 0 0 x y))) :=
      augmentationChainMap_mk augmentation I (A.mul 0 0 x y)
    _ = Ideal.Quotient.mk (I.map (algebraMap R S))
        ((degreeZeroIso R S).hom (augmentation.toChainMap.f 0 x) *
          (degreeZeroIso R S).hom (augmentation.toChainMap.f 0 y)) :=
      congrArg (Ideal.Quotient.mk (I.map (algebraMap R S))) (augmentation.map_mul x y)
    _ = _ := (map_mul (Ideal.Quotient.mk (I.map (algebraMap R S))) _ _).trans
      (congrArg₂ (fun a b : S ⧸ I.map (algebraMap R S) ↦ a * b)
        (augmentationChainMap_mk augmentation I x).symm
        (augmentationChainMap_mk augmentation I y).symm)

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
        ((degreeZeroIso R S).hom (augmentation.toChainMap.f 0 x)) :=
  IdealQuotient.augmentationChainMap_mk augmentation I x

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
          ((A.quotientByIdeal I).iCycles 0 x)) :=
  (augmentation.quotientByIdeal I).homologyZeroMap_homologyπ x

/-- On any degree-zero element that is a cycle, the homology augmentation is the original
chain-map component; no DGA homomorphism in other degrees is used. -/
theorem homologyZeroMap_degreeZeroClassMap (augmentation : Augmentation A S)
    (hd : A.toChainComplex.d 0 (-1) = 0) (x : A.X 0) :
    augmentation.homologyZeroMap (A.toChainComplex.degreeZeroClassMap hd x) =
      (degreeZeroIso R S).hom (augmentation.toChainMap.f 0 x) := by
  change augmentation.homologyZeroMap
    (A.homologyπ 0 (A.toChainComplex.liftCycles (𝟙 _) (-1)
      (by apply (ComplexShape.down ℤ).next_eq'; decide) (by simp [hd]) x)) = _
  rw [homologyZeroMap_homologyπ]
  have hi := ConcreteCategory.congr_hom
    (A.toChainComplex.liftCycles_i (𝟙 _) (-1)
      (by apply (ComplexShape.down ℤ).next_eq'; decide) (by simp [hd])) x
  exact congrArg (fun z ↦ (degreeZeroIso R S).hom (augmentation.toChainMap.f 0 z)) hi

/-- For a nonnegative DGA whose augmentation identifies zeroth homology with `S`, quotienting by
a base ideal identifies zeroth homology with the corresponding quotient of `S`. -/
theorem quotientHomologyZeroMap_bijective (augmentation : Augmentation A S)
    [A.IsNonnegative]
    (hH0 : Function.Bijective augmentation.homologyZeroMap) (I : Ideal R) :
    Function.Bijective (augmentation.quotientHomologyZeroMap I) := by
  have hd : A.toChainComplex.d 0 (-1) = 0 :=
    (A.isZero_X_of_neg (-1) (by decide)).eq_of_tgt _ _
  have hdQ : (A.quotientByIdeal I).toChainComplex.d 0 (-1) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := IdealQuotient.mk_surjective A I 0 x
    have hx : A.d 0 x = 0 := ConcreteCategory.congr_hom hd x
    change (A.quotientByIdeal I).d 0 (IdealQuotient.mk A I 0 x) = 0
    calc
      _ = IdealQuotient.mk A I (-1) (A.d 0 x) := IdealQuotient.d_mk A I 0 x
      _ = 0 := by rw [hx, IdealQuotient.mk_eq_quotient_mk]; rfl
  let p := A.toChainComplex.degreeZeroClassMap hd
  let q := (A.quotientByIdeal I).toChainComplex.degreeZeroClassMap hdQ
  let e : A.X 0 →ₗ[R] S := augmentation.homologyZeroMap.toLinearMap.comp p
  have he : Function.Surjective e := hH0.2.comp
    (A.toChainComplex.degreeZeroClassMap_surjective hd)
  have hq : Function.Surjective q :=
    (A.quotientByIdeal I).toChainComplex.degreeZeroClassMap_surjective hdQ
  have hcomp (x : A.X 0) :
      augmentation.quotientHomologyZeroMap I (q (IdealQuotient.mk A I 0 x)) =
        Ideal.Quotient.mk (I.map (algebraMap R S)) (e x) := by
    change (augmentation.quotientByIdeal I).homologyZeroMap
      ((A.quotientByIdeal I).toChainComplex.degreeZeroClassMap hdQ
        (IdealQuotient.mk A I 0 x)) = _
    rw [homologyZeroMap_degreeZeroClassMap, quotientByIdeal_mk]
    exact congrArg (Ideal.Quotient.mk (I.map (algebraMap R S)))
      (homologyZeroMap_degreeZeroClassMap augmentation hd x).symm
  constructor
  · apply (injective_iff_map_eq_zero (augmentation.quotientHomologyZeroMap I)).mpr
    intro z hz
    obtain ⟨x, rfl⟩ := hq z
    obtain ⟨x, rfl⟩ := IdealQuotient.mk_surjective A I 0 x
    have hx0 : Ideal.Quotient.mk (I.map (algebraMap R S)) (e x) = 0 :=
      (hcomp x).symm.trans hz
    have hxI : e x ∈ I • (⊤ : Submodule R S) := by
      apply (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule R S))).mp
      apply (Ideal.Quotient.Map.idealQuotientEquiv (R := R) (S := S) I).injective
      rw [Ideal.Quotient.Map.idealQuotientEquiv_apply_mk, map_zero]
      exact hx0
    have hsup : x ∈ I • (⊤ : Submodule R (A.X 0)) ⊔ LinearMap.ker e := by
      rw [← Submodule.comap_smul_top_of_surjective I e he]
      exact hxI
    obtain ⟨w, hw, z, hz, hsum⟩ := Submodule.mem_sup.mp hsup
    have hpz : p z = 0 := hH0.1
      ((show augmentation.homologyZeroMap (p z) = 0 from hz).trans
        (map_zero augmentation.homologyZeroMap).symm)
    obtain ⟨y, hy⟩ := (A.toChainComplex.degreeZeroClassMap_zero_iff hd z).mp hpz
    have hw0 : q (IdealQuotient.mk A I 0 w) = 0 := by
      have hwq : IdealQuotient.mk A I 0 w = 0 :=
        (IdealQuotient.mk_eq_quotient_mk A I 0 w).trans
          ((Submodule.Quotient.mk_eq_zero _).mpr hw)
      exact (congrArg q hwq).trans q.map_zero
    have hz0 : q (IdealQuotient.mk A I 0 z) = 0 := by
      calc
        _ = q (IdealQuotient.mk A I 0 (A.d 1 y)) := congrArg
          (fun a ↦ q (IdealQuotient.mk A I 0 a)) hy.symm
        _ = q ((A.quotientByIdeal I).d 1 (IdealQuotient.mk A I 1 y)) :=
          congrArg q (IdealQuotient.d_mk A I 1 y).symm
        _ = 0 := (A.quotientByIdeal I).toChainComplex.degreeZeroClassMap_boundary hdQ _
    rw [← hsum]
    calc
      _ = q (IdealQuotient.mk A I 0 w + IdealQuotient.mk A I 0 z) :=
        congrArg q ((ChainGradedAlgebra.IdealQuotient.mk A.toChainGradedAlgebra I 0).map_add w z)
      _ = q (IdealQuotient.mk A I 0 w) + q (IdealQuotient.mk A I 0 z) := q.map_add _ _
      _ = 0 := (congrArg₂ (fun a b ↦ a + b) hw0 hz0).trans (zero_add 0)
  · intro s
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
    obtain ⟨x, rfl⟩ := he s
    exact ⟨q (IdealQuotient.mk A I 0 x), hcomp x⟩

end Augmentation

end ChainDGAlgebra

/- The scalar tower for each quotient homogeneous component is supplied by the neutral quotient
module owner, rather than by a DGA-specific instance. -/
