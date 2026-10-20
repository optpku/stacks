module

public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import Mathlib.Algebra.Field.ULift
public import stacks_project.Chap45.Proposition_45_12_4
public import stacks_project.Chap50.Lemma_50_21_1_DeRhamTheory
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CanonicalAction

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u moduleUniverse

namespace AlgebraicGeometry.Scheme

/-- The full subcategory of qcqs schemes over the universe-lifted rational field. -/
def QcqsOverQ : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun X : SchemeOverField (ULift.{u} ℚ) ↦ IsQcqs X.left)

namespace QcqsOverQ

/-- The category structure inherited by qcqs schemes over `ℚ`. -/
instance category : Category.{u} QcqsOverQ.{u} :=
  inferInstanceAs (Category.{u} (ObjectProperty.FullSubcategory
    (fun X : SchemeOverField (ULift.{u} ℚ) ↦ IsQcqs X.left)))

/-- Regard a qcqs scheme over `ℚ` as an object of `QcqsOverQ`. -/
def of (X : SchemeOverField (ULift.{u} ℚ)) [IsQcqs X.left] : QcqsOverQ.{u} :=
  ⟨X, inferInstance⟩

/-- The object underlying `QcqsOverQ.of X` is the supplied scheme over `ℚ`. -/
theorem of_obj (X : SchemeOverField (ULift.{u} ℚ)) [IsQcqs X.left] :
    (of X).obj = X := sorry

/-- Every object of `QcqsOverQ` has a qcqs underlying scheme. -/
instance isQcqs (X : QcqsOverQ.{u}) : IsQcqs X.obj.left := X.property

/-- The forgetful functor from qcqs schemes over `ℚ` to schemes. -/
def toScheme : QcqsOverQ.{u} ⥤ Scheme.{u} :=
  ObjectProperty.ι (fun X : SchemeOverField (ULift.{u} ℚ) ↦ IsQcqs X.left) ⋙
    Over.forget _

/-- The forgetful functor sends an object to its underlying scheme. -/
theorem toScheme_obj (X : QcqsOverQ.{u}) : toScheme.obj X = X.obj.left := sorry

end QcqsOverQ

namespace DeRham

/-- Relative de Rham cohomology over `ℚ` in even degree `2 * i`. -/
noncomputable abbrev rationalEvenCohomology (X : QcqsOverQ.{u}) (i : ℕ) : Type u :=
  cohomologyOverAffineBase X.obj.hom (2 * (i : ℤ))

/-- Rational even de Rham cohomology uses cohomological degree `2 * i`. -/
theorem rationalEvenCohomology_def (X : QcqsOverQ.{u}) (i : ℕ) :
    rationalEvenCohomology X i =
      cohomologyOverAffineBase X.obj.hom (2 * (i : ℤ)) := sorry

/-- The binary biproduct presentation used by rational relative de Rham comparisons. -/
noncomputable instance rationalCoefficientHasBinaryBiproducts (X : QcqsOverQ.{u}) :
    HasBinaryBiproducts
      (RingedSite.ModuleCat.{max u moduleUniverse}
        (RingedSpace.DeRham.coefficientSite X.obj.hom.toLRSHom.toShHom)) :=
  @Abelian.hasBinaryBiproducts _ _
    (RingedSite.moduleCatAbelian.{max u moduleUniverse}
      (RingedSpace.DeRham.coefficientSite X.obj.hom.toLRSHom.toShHom))

/-- The graded tensor coproducts for rational relative coefficient modules. -/
instance rationalCoefficientGradedHasTensor (X : QcqsOverQ.{u}) :
    ∀ G₁ G₂ : GradedObject ℤ
      (RingedSpace.DeRham.coefficientSite X.obj.hom.toLRSHom.toShHom).ModuleCat,
      GradedObject.HasTensor G₁ G₂ :=
  fun G₁ G₂ j ↦ hasColimitOfHasColimitsOfShape
    (Discrete.functor
      ((((GradedObject.mapBifunctor
        (MonoidalCategory.curriedTensor _) ℤ ℤ).obj G₁).obj G₂).mapObjFun
          (fun x ↦ x.1 + x.2) j))

/-- The canonical constant-one class in relative degree zero. -/
noncomputable def rationalCohomologyOne (X : QcqsOverQ.{u}) :
    cohomology X.obj.hom 0 := ClassAction.cohomologyOneCanonical X.obj.hom

/-- The relative unit is the constant-one class of its de Rham complex. -/
theorem rationalCohomologyOne_def (X : QcqsOverQ.{u}) :
    rationalCohomologyOne X = ClassAction.cohomologyOneCanonical X.obj.hom := rfl

/-- A morphism of schemes over `ℚ` gives the canonical square between their structure maps. -/
theorem rationalCommSq {X' X : QcqsOverQ.{u}} (f : X' ⟶ X) :
    CommSq (QcqsOverQ.toScheme.map f) X'.obj.hom X.obj.hom (𝟙 _) := sorry

/-- An explicit realization of the Chern-class theory by even relative de Rham cohomology
over `ℚ`. Its operations and comparison maps are data, while compatibility is propositional. -/
structure RationalChernTheory.{v} where
  /-- The contravariant graded cohomology algebra. -/
  A : QcqsOverQ.{v}ᵒᵖ ⥤ RingCat.{v}
  /-- The nonnegative homogeneous pieces of the cohomology algebra. -/
  Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X))
  /-- The graded-algebra structure on each value. -/
  gradedAlgebra : ∀ X, GradedAlgebra (Agrade X)
  /-- The rational algebra structure on each value. -/
  algebra : ∀ X, Algebra ℚ (A.obj (Opposite.op X))
  /-- The Chern-class theory axioms. -/
  toTheory : @ChernClass.CohomologyTheory QcqsOverQ _ QcqsOverQ.toScheme A Agrade gradedAlgebra
  /-- Identification of degree `i` with `H_dR^(2i)(X/ℚ)`. -/
  componentEquiv : ∀ X i, Agrade X i ≃+ rationalEvenCohomology X i
  /-- The canonical constant-one class in relative degree zero. -/
  cohomologyUnit : ∀ (X : QcqsOverQ.{v}), cohomology X.obj.hom 0
  /-- The degree-zero class is the constant-one class from the relative de Rham complex. -/
  cohomologyUnit_eq : ∀ (X : QcqsOverQ.{v}), cohomologyUnit X =
    rationalCohomologyOne X
  /-- The canonical unit family in even relative de Rham cohomology. -/
  deRhamUnit : ∀ (X : QcqsOverQ.{v}), ∀ i, rationalEvenCohomology X i
  /-- The degree-zero component of the unit family is the constant-one class. -/
  deRhamUnit_zero : ∀ (X : QcqsOverQ.{v}), deRhamUnit X 0 = cohomologyUnit X
  /-- Every positive-degree component of the unit family vanishes. -/
  deRhamUnit_succ : ∀ (X : QcqsOverQ.{v}) i, deRhamUnit X (i + 1) = 0
  /-- The relative cup product before reindexing the even degrees. -/
  cohomologyCupProduct : ∀ (X : QcqsOverQ.{v}) (i j : ℕ),
    MonoidalCategoryStruct.tensorObj
        (cohomology X.obj.hom (2 * (i : ℤ)))
        (cohomology X.obj.hom (2 * (j : ℤ))) ⟶
      cohomology X.obj.hom (2 * (i : ℤ) + 2 * (j : ℤ))
  /-- The displayed product is the wedge-induced relative cup product. -/
  cohomologyCupProduct_eq : ∀ (X : QcqsOverQ.{v}) (i j : ℕ),
    cohomologyCupProduct X i j =
      CanonicalAction.cupMorphism X.obj.hom (2 * (i : ℤ)) (2 * (j : ℤ))
  /-- The binary even-degree cup product. -/
  cupProduct : ∀ (X : QcqsOverQ.{v}) {i j n : ℕ}, i + j = n →
    rationalEvenCohomology X i → rationalEvenCohomology X j →
      rationalEvenCohomology X n
  /-- Reindexing the relative cup product gives the binary even-degree operation. -/
  cupProduct_eq : ∀ (X : QcqsOverQ.{v}) {i j n : ℕ} (h : i + j = n)
      (a : rationalEvenCohomology X i) (b : rationalEvenCohomology X j),
    HEq (cupProduct X h a b)
      ((cohomologyCupProduct X i j).hom
        (TensorProduct.tmul (coefficientRing X.obj.hom) a b))
  /-- Cup-product convolution on families of even relative de Rham classes. -/
  cupProductConvolution : ∀ (X : QcqsOverQ.{v}),
    (∀ i, rationalEvenCohomology X i) → (∀ i, rationalEvenCohomology X i) →
      ∀ i, rationalEvenCohomology X i
  /-- The family product is the finite convolution of the concrete cup products. -/
  cupProductConvolution_component : ∀ (X : QcqsOverQ.{v})
      (a b : ∀ i, rationalEvenCohomology X i) (n : ℕ),
    cupProductConvolution X a b n =
      ∑ k : Fin (n + 1), cupProduct X
        (Nat.add_sub_of_le (Nat.le_of_lt_succ k.isLt)) (a k) (b (n - k))
  /-- Coefficients of the abstract unit lie in their homogeneous pieces. -/
  oneCoeff_mem : ∀ (X : QcqsOverQ.{v}) i,
    PowerSeries.coeff i (1 : PowerSeries (A.obj (Opposite.op X))) ∈ Agrade X i
  /-- The degree equivalences transport the abstract unit to the relative de Rham unit. -/
  unit_component : ∀ (X : QcqsOverQ.{v}) i,
    componentEquiv X i ⟨PowerSeries.coeff i 1, oneCoeff_mem X i⟩ = deRhamUnit X i
  /-- Products of homogeneous series again have homogeneous coefficients. -/
  mulCoeff_mem : ∀ (X : QcqsOverQ.{v}) (a b : PowerSeries (A.obj (Opposite.op X))),
    (∀ i, PowerSeries.coeff i a ∈ Agrade X i) →
    (∀ i, PowerSeries.coeff i b ∈ Agrade X i) →
    ∀ i, PowerSeries.coeff i (a * b) ∈ Agrade X i
  /-- Abstract multiplication transports to relative cup-product convolution. -/
  mul_component : ∀ (X : QcqsOverQ.{v})
      (a b : PowerSeries (A.obj (Opposite.op X)))
      (ha : ∀ i, PowerSeries.coeff i a ∈ Agrade X i)
      (hb : ∀ i, PowerSeries.coeff i b ∈ Agrade X i) (n : ℕ),
    componentEquiv X n ⟨PowerSeries.coeff n (a * b), mulCoeff_mem X a b ha hb n⟩ =
      cupProductConvolution X
        (fun i ↦ componentEquiv X i ⟨PowerSeries.coeff i a, ha i⟩)
        (fun i ↦ componentEquiv X i ⟨PowerSeries.coeff i b, hb i⟩) n
  /-- Pullback on even relative de Rham groups. -/
  deRhamPullback : ∀ {X' X : QcqsOverQ.{v}}, (X' ⟶ X) → ∀ i,
    rationalEvenCohomology X i →+ rationalEvenCohomology X' i
  /-- The right-derived comparison constructing relative de Rham pullback. -/
  pullbackDerived : ∀ {X' X : QcqsOverQ.{v}} (f : X' ⟶ X),
    Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived
        (Cohomology.coefficientHom (rationalCommSq f)))
      (RingedSite.Hom.ModuleQis
        (RingedSpace.DeRham.coefficientSite X'.obj.hom.toLRSHom.toShHom))
  /-- The displayed map is induced by the relative de Rham pullback comparison. -/
  deRhamPullback_eq : ∀ {X' X : QcqsOverQ.{v}} (f : X' ⟶ X) (i : ℕ)
      (a : rationalEvenCohomology X i),
    deRhamPullback f i a =
      (@Cohomology.restrictedPullback _ _ _ _ _ _ _ _
        (rationalCommSq f) (2 * (i : ℤ)) (pullbackDerived f)).hom a
  /-- The degree equivalences identify algebra pullback with relative de Rham pullback. -/
  pullback_component : ∀ {X' X : QcqsOverQ.{v}} (f : X' ⟶ X) (i : ℕ)
      (a : Agrade X i),
    deRhamPullback f i (componentEquiv X i a) =
      componentEquiv X' i ⟨A.map f.op a, toTheory.pullback_mem f i a⟩
  /-- The relative de Rham first-Chern and cup-product context. -/
  chernClass : ∀ (X : QcqsOverQ.{v}), ChernClassContext X.obj.hom
  /-- The Chapter 50 pullback comparison between relative de Rham contexts. -/
  chernPullback : ∀ {X' X : QcqsOverQ.{v}} (f : X' ⟶ X),
    ChernClassContext.Pullback (rationalCommSq f) (chernClass X) (chernClass X')
  /-- General pullback specializes in degree one to the first-Chern pullback map. -/
  pullback_degree_one : ∀ {X' X : QcqsOverQ.{v}} (f : X' ⟶ X)
      (a : rationalEvenCohomology X 1),
    deRhamPullback f 1 a = (chernPullback f).deRhamPullback a
  /-- The abstract and relative de Rham first Chern classes agree. -/
  firstChernClass_component : ∀ (X : QcqsOverQ.{v})
      (L : (QcqsOverQ.toScheme.obj X).PicardGroup),
    componentEquiv X 1 (toTheory.firstChernClass X L) =
      (chernClass X).deRhamFirstChern L

namespace RationalChernTheory

/-- Build a rational relative de Rham realization from all its explicit data and laws. -/
def ofRealization
    (A : QcqsOverQ.{u}ᵒᵖ ⥤ RingCat.{u})
    (Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X)))
    (gradedAlgebra : ∀ X, GradedAlgebra (Agrade X))
    (algebra : ∀ X, Algebra ℚ (A.obj (Opposite.op X)))
    (toTheory : @ChernClass.CohomologyTheory QcqsOverQ _ QcqsOverQ.toScheme
      A Agrade gradedAlgebra)
    (componentEquiv : ∀ X i, Agrade X i ≃+ rationalEvenCohomology X i)
    (cohomologyUnit : ∀ X : QcqsOverQ.{u}, cohomology X.obj.hom 0)
    (cohomologyUnit_eq : ∀ X : QcqsOverQ.{u}, cohomologyUnit X =
      rationalCohomologyOne X)
    (deRhamUnit : ∀ X : QcqsOverQ.{u}, ∀ i, rationalEvenCohomology X i)
    (deRhamUnit_zero : ∀ X : QcqsOverQ.{u}, deRhamUnit X 0 = cohomologyUnit X)
    (deRhamUnit_succ : ∀ (X : QcqsOverQ.{u}) i, deRhamUnit X (i + 1) = 0)
    (cohomologyCupProduct : ∀ (X : QcqsOverQ.{u}) (i j : ℕ),
      MonoidalCategoryStruct.tensorObj
          (cohomology X.obj.hom (2 * (i : ℤ)))
          (cohomology X.obj.hom (2 * (j : ℤ))) ⟶
        cohomology X.obj.hom (2 * (i : ℤ) + 2 * (j : ℤ)))
    (cohomologyCupProduct_eq : ∀ (X : QcqsOverQ.{u}) (i j : ℕ),
      cohomologyCupProduct X i j =
        CanonicalAction.cupMorphism X.obj.hom (2 * (i : ℤ)) (2 * (j : ℤ)))
    (cupProduct : ∀ (X : QcqsOverQ.{u}) {i j n : ℕ}, i + j = n →
      rationalEvenCohomology X i → rationalEvenCohomology X j →
        rationalEvenCohomology X n)
    (cupProduct_eq : ∀ (X : QcqsOverQ.{u}) {i j n : ℕ} (h : i + j = n)
        (a : rationalEvenCohomology X i) (b : rationalEvenCohomology X j),
      HEq (cupProduct X h a b)
        ((cohomologyCupProduct X i j).hom
          (TensorProduct.tmul (coefficientRing X.obj.hom) a b)))
    (cupProductConvolution : ∀ X : QcqsOverQ.{u},
      (∀ i, rationalEvenCohomology X i) → (∀ i, rationalEvenCohomology X i) →
        ∀ i, rationalEvenCohomology X i)
    (cupProductConvolution_component : ∀ (X : QcqsOverQ.{u})
        (a b : ∀ i, rationalEvenCohomology X i) (n : ℕ),
      cupProductConvolution X a b n =
        ∑ k : Fin (n + 1), cupProduct X
          (Nat.add_sub_of_le (Nat.le_of_lt_succ k.isLt)) (a k) (b (n - k)))
    (oneCoeff_mem : ∀ (X : QcqsOverQ.{u}) i,
      PowerSeries.coeff i (1 : PowerSeries (A.obj (Opposite.op X))) ∈ Agrade X i)
    (unit_component : ∀ (X : QcqsOverQ.{u}) i,
      componentEquiv X i ⟨PowerSeries.coeff i 1, oneCoeff_mem X i⟩ = deRhamUnit X i)
    (mulCoeff_mem : ∀ (X : QcqsOverQ.{u})
        (a b : PowerSeries (A.obj (Opposite.op X))),
      (∀ i, PowerSeries.coeff i a ∈ Agrade X i) →
      (∀ i, PowerSeries.coeff i b ∈ Agrade X i) →
      ∀ i, PowerSeries.coeff i (a * b) ∈ Agrade X i)
    (mul_component : ∀ (X : QcqsOverQ.{u})
        (a b : PowerSeries (A.obj (Opposite.op X)))
        (ha : ∀ i, PowerSeries.coeff i a ∈ Agrade X i)
        (hb : ∀ i, PowerSeries.coeff i b ∈ Agrade X i) (n : ℕ),
      componentEquiv X n
          ⟨PowerSeries.coeff n (a * b), mulCoeff_mem X a b ha hb n⟩ =
        cupProductConvolution X
          (fun i ↦ componentEquiv X i ⟨PowerSeries.coeff i a, ha i⟩)
          (fun i ↦ componentEquiv X i ⟨PowerSeries.coeff i b, hb i⟩) n)
    (deRhamPullback : ∀ {X' X : QcqsOverQ.{u}}, (X' ⟶ X) → ∀ i,
      rationalEvenCohomology X i →+ rationalEvenCohomology X' i)
    (pullbackDerived : ∀ {X' X : QcqsOverQ.{u}} (f : X' ⟶ X),
      Functor.HasRightDerivedFunctor
        (RingedSite.Hom.modulePushforwardToDerived
          (Cohomology.coefficientHom (rationalCommSq f)))
        (RingedSite.Hom.ModuleQis
          (RingedSpace.DeRham.coefficientSite X'.obj.hom.toLRSHom.toShHom)))
    (deRhamPullback_eq : ∀ {X' X : QcqsOverQ.{u}} (f : X' ⟶ X) (i : ℕ)
        (a : rationalEvenCohomology X i),
      deRhamPullback f i a =
        (@Cohomology.restrictedPullback _ _ _ _ _ _ _ _
          (rationalCommSq f) (2 * (i : ℤ)) (pullbackDerived f)).hom a)
    (pullback_component : ∀ {X' X : QcqsOverQ.{u}} (f : X' ⟶ X) (i : ℕ)
        (a : Agrade X i),
      deRhamPullback f i (componentEquiv X i a) =
        componentEquiv X' i ⟨A.map f.op a, toTheory.pullback_mem f i a⟩)
    (chernClass : ∀ X : QcqsOverQ.{u}, ChernClassContext X.obj.hom)
    (chernPullback : ∀ {X' X : QcqsOverQ.{u}} (f : X' ⟶ X),
      ChernClassContext.Pullback (rationalCommSq f) (chernClass X) (chernClass X'))
    (pullback_degree_one : ∀ {X' X : QcqsOverQ.{u}} (f : X' ⟶ X)
        (a : rationalEvenCohomology X 1),
      deRhamPullback f 1 a = (chernPullback f).deRhamPullback a)
    (firstChernClass_component : ∀ (X : QcqsOverQ.{u})
        (L : (QcqsOverQ.toScheme.obj X).PicardGroup),
      componentEquiv X 1 (toTheory.firstChernClass X L) =
        (chernClass X).deRhamFirstChern L) : RationalChernTheory.{u} where
  A := A
  Agrade := Agrade
  gradedAlgebra := gradedAlgebra
  algebra := algebra
  toTheory := toTheory
  componentEquiv := componentEquiv
  cohomologyUnit := cohomologyUnit
  cohomologyUnit_eq := cohomologyUnit_eq
  deRhamUnit := deRhamUnit
  deRhamUnit_zero := deRhamUnit_zero
  deRhamUnit_succ := deRhamUnit_succ
  cohomologyCupProduct := cohomologyCupProduct
  cohomologyCupProduct_eq := cohomologyCupProduct_eq
  cupProduct := cupProduct
  cupProduct_eq := cupProduct_eq
  cupProductConvolution := cupProductConvolution
  cupProductConvolution_component := cupProductConvolution_component
  oneCoeff_mem := oneCoeff_mem
  unit_component := unit_component
  mulCoeff_mem := mulCoeff_mem
  mul_component := mul_component
  deRhamPullback := deRhamPullback
  pullbackDerived := pullbackDerived
  deRhamPullback_eq := deRhamPullback_eq
  pullback_component := pullback_component
  chernClass := chernClass
  chernPullback := chernPullback
  pullback_degree_one := pullback_degree_one
  firstChernClass_component := firstChernClass_component

/-- The family unit is the transported abstract unit. -/
theorem unit_spec (D : RationalChernTheory.{u}) (X : QcqsOverQ.{u}) (i : ℕ) :
    D.componentEquiv X i ⟨PowerSeries.coeff i 1, D.oneCoeff_mem X i⟩ =
      D.deRhamUnit X i := sorry

/-- Abstract multiplication is transported to relative de Rham cup convolution. -/
theorem multiplication_spec (D : RationalChernTheory.{u}) (X : QcqsOverQ.{u})
    (a b : PowerSeries (D.A.obj (Opposite.op X)))
    (ha : ∀ i, PowerSeries.coeff i a ∈ D.Agrade X i)
    (hb : ∀ i, PowerSeries.coeff i b ∈ D.Agrade X i) (n : ℕ) :
    D.componentEquiv X n
        ⟨PowerSeries.coeff n (a * b), D.mulCoeff_mem X a b ha hb n⟩ =
      D.cupProductConvolution X
        (fun i ↦ D.componentEquiv X i ⟨PowerSeries.coeff i a, ha i⟩)
        (fun i ↦ D.componentEquiv X i ⟨PowerSeries.coeff i b, hb i⟩) n := sorry

/-- Abstract pullback is transported to relative de Rham pullback in every even degree. -/
theorem pullback_spec (D : RationalChernTheory.{u}) {X' X : QcqsOverQ.{u}}
    (f : X' ⟶ X) (i : ℕ) (a : D.Agrade X i) :
    D.deRhamPullback f i (D.componentEquiv X i a) =
      D.componentEquiv X' i
        ⟨D.A.map f.op a,
          @ChernClass.CohomologyTheory.pullback_mem _ _ QcqsOverQ.toScheme D.A D.Agrade
            D.gradedAlgebra D.toTheory X' X f i a⟩ := sorry

/-- The transported first Chern class is the Chapter 50 relative de Rham class. -/
theorem firstChernClass_spec (D : RationalChernTheory.{u}) (X : QcqsOverQ.{u})
    (L : X.obj.left.PicardGroup) :
    D.componentEquiv X 1
        (@ChernClass.CohomologyTheory.firstChernClass _ _ QcqsOverQ.toScheme D.A D.Agrade
          D.gradedAlgebra D.toTheory X L) =
      (D.chernClass X).deRhamFirstChern L := sorry

/-- The graded first Chern class carried by a rational de Rham realization. -/
def gradedFirstChernClass (D : RationalChernTheory.{u}) :
    ∀ X, (QcqsOverQ.toScheme.obj X).PicardGroup →+ D.Agrade X 1 :=
  @ChernClass.CohomologyTheory.firstChernClass _ _ QcqsOverQ.toScheme D.A D.Agrade
    D.gradedAlgebra D.toTheory

/-- `gradedFirstChernClass` is the first Chern class of the underlying theory. -/
theorem gradedFirstChernClass_apply (D : RationalChernTheory.{u})
    (X : QcqsOverQ.{u}) (L : (QcqsOverQ.toScheme.obj X).PicardGroup) :
    D.gradedFirstChernClass X L =
      @ChernClass.CohomologyTheory.firstChernClass _ _ QcqsOverQ.toScheme D.A D.Agrade
        D.gradedAlgebra D.toTheory X L := sorry

end RationalChernTheory

end DeRham

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ChernClass.ChernCharacter

open Scheme Scheme.DeRham

/-- The concrete even relative de Rham components of a rational Chern character. -/
def deRhamApp (D : RationalChernTheory.{u})
    (ch : @ChernClass.ChernCharacter QcqsOverQ _ QcqsOverQ.toScheme
      D.A D.Agrade D.gradedAlgebra D.gradedFirstChernClass D.algebra)
    (X : QcqsOverQ.{u}) (alpha : Scheme.VectorBundleK0 X.obj.left) :
    ∀ i, rationalEvenCohomology X i :=
  fun i ↦ D.componentEquiv X i
    ⟨PowerSeries.coeff i
        (@ChernClass.ChernCharacter.app _ _ QcqsOverQ.toScheme D.A D.Agrade
          D.gradedAlgebra D.gradedFirstChernClass D.algebra ch X alpha),
      @ChernClass.ChernCharacter.coeff_mem _ _ QcqsOverQ.toScheme D.A D.Agrade
        D.gradedAlgebra D.gradedFirstChernClass D.algebra ch X alpha i⟩

/-- Evaluation of `deRhamApp` is transport of a homogeneous power-series coefficient. -/
theorem deRhamApp_apply (D : RationalChernTheory.{u})
    (ch : @ChernClass.ChernCharacter QcqsOverQ _ QcqsOverQ.toScheme
      D.A D.Agrade D.gradedAlgebra D.gradedFirstChernClass D.algebra)
    (X : QcqsOverQ.{u}) (alpha : Scheme.VectorBundleK0 X.obj.left) (i : ℕ) :
    deRhamApp D ch X alpha i = D.componentEquiv X i
      ⟨PowerSeries.coeff i
          (@ChernClass.ChernCharacter.app _ _ QcqsOverQ.toScheme D.A D.Agrade
            D.gradedAlgebra D.gradedFirstChernClass D.algebra ch X alpha),
        @ChernClass.ChernCharacter.coeff_mem _ _ QcqsOverQ.toScheme D.A D.Agrade
          D.gradedAlgebra D.gradedFirstChernClass D.algebra ch X alpha i⟩ := sorry

/-- The zero `K₀`-class has zero in every relative de Rham component. -/
theorem deRhamApp_zero (D : RationalChernTheory.{u})
    (ch : @ChernClass.ChernCharacter QcqsOverQ _ QcqsOverQ.toScheme
      D.A D.Agrade D.gradedAlgebra D.gradedFirstChernClass D.algebra)
    (X : QcqsOverQ.{u}) (i : ℕ) : deRhamApp D ch X 0 i = 0 := sorry

/-- The multiplicative unit has the canonical relative de Rham unit family. -/
theorem deRhamApp_one (D : RationalChernTheory.{u})
    (ch : @ChernClass.ChernCharacter QcqsOverQ _ QcqsOverQ.toScheme
      D.A D.Agrade D.gradedAlgebra D.gradedFirstChernClass D.algebra)
    (X : QcqsOverQ.{u}) (i : ℕ) :
    deRhamApp D ch X 1 i = D.deRhamUnit X i := sorry

/-- Addition of `K₀`-classes is componentwise addition in relative de Rham cohomology. -/
theorem deRhamApp_add (D : RationalChernTheory.{u})
    (ch : @ChernClass.ChernCharacter QcqsOverQ _ QcqsOverQ.toScheme
      D.A D.Agrade D.gradedAlgebra D.gradedFirstChernClass D.algebra)
    (X : QcqsOverQ.{u}) (alpha beta : Scheme.VectorBundleK0 X.obj.left) (i : ℕ) :
    deRhamApp D ch X (alpha + beta) i =
      deRhamApp D ch X alpha i + deRhamApp D ch X beta i := sorry

/-- Multiplication of `K₀`-classes becomes relative cup-product convolution. -/
theorem deRhamApp_mul (D : RationalChernTheory.{u})
    (ch : @ChernClass.ChernCharacter QcqsOverQ _ QcqsOverQ.toScheme
      D.A D.Agrade D.gradedAlgebra D.gradedFirstChernClass D.algebra)
    (X : QcqsOverQ.{u}) (alpha beta : Scheme.VectorBundleK0 X.obj.left) :
    deRhamApp D ch X (alpha * beta) =
      D.cupProductConvolution X (deRhamApp D ch X alpha) (deRhamApp D ch X beta) := sorry

/-- Pullback of `K₀`-classes agrees degreewise with relative de Rham pullback. -/
theorem deRhamApp_naturality (D : RationalChernTheory.{u})
    (ch : @ChernClass.ChernCharacter QcqsOverQ _ QcqsOverQ.toScheme
      D.A D.Agrade D.gradedAlgebra D.gradedFirstChernClass D.algebra)
    {X' X : QcqsOverQ.{u}} (f : X' ⟶ X)
    (alpha : Scheme.VectorBundleK0 X.obj.left) (i : ℕ) :
    D.deRhamPullback f i (deRhamApp D ch X alpha i) =
      deRhamApp D ch X'
        (Scheme.VectorBundleK0.pullback (QcqsOverQ.toScheme.map f) alpha) i := sorry

/-- Every coefficient of the formal exponential of the graded first Chern class is
homogeneous of its indicated degree. -/
theorem expCoeff_mem (D : RationalChernTheory.{u}) (X : QcqsOverQ.{u})
    (L : X.obj.left.PicardGroup) (i : ℕ) :
    PowerSeries.coeff i
        (@exp _ inferInstance (D.algebra X)
          (D.gradedFirstChernClass X L : D.A.obj (Opposite.op X))) ∈
      D.Agrade X i := sorry

/-- The concrete relative de Rham exponential of the first Chern class of a line bundle. -/
def deRhamExp (D : RationalChernTheory.{u}) (X : QcqsOverQ.{u})
    (L : X.obj.left.PicardGroup) : ∀ i, rationalEvenCohomology X i :=
  fun i ↦ D.componentEquiv X i
    ⟨PowerSeries.coeff i
      (@exp _ inferInstance (D.algebra X)
        (D.gradedFirstChernClass X L : D.A.obj (Opposite.op X))),
      expCoeff_mem D X L i⟩

/-- The `i`-th component of `deRhamExp` is the transported exponential coefficient. -/
theorem deRhamExp_apply (D : RationalChernTheory.{u}) (X : QcqsOverQ.{u})
    (L : X.obj.left.PicardGroup) (i : ℕ) :
    deRhamExp D X L i = D.componentEquiv X i
      ⟨PowerSeries.coeff i
        (@exp _ inferInstance (D.algebra X)
          (D.gradedFirstChernClass X L : D.A.obj (Opposite.op X))),
        expCoeff_mem D X L i⟩ := sorry

/-- The factorial-normalized power of the first Chern class is homogeneous of degree `i`. -/
theorem expCoeffFormula_mem (D : RationalChernTheory.{u}) (X : QcqsOverQ.{u})
    (L : X.obj.left.PicardGroup) (i : ℕ) :
    (D.algebra X).algebraMap ((i.factorial : ℚ)⁻¹) *
        (D.gradedFirstChernClass X L : D.A.obj (Opposite.op X)) ^ i ∈
      D.Agrade X i := sorry

/-- The exponential coefficient is `c₁(L) ^ i / i!` before transport to de Rham cohomology. -/
theorem deRhamExp_coeff (D : RationalChernTheory.{u}) (X : QcqsOverQ.{u})
    (L : X.obj.left.PicardGroup) (i : ℕ) :
    deRhamExp D X L i = D.componentEquiv X i
      ⟨(D.algebra X).algebraMap ((i.factorial : ℚ)⁻¹) *
          (D.gradedFirstChernClass X L : D.A.obj (Opposite.op X)) ^ i,
        expCoeffFormula_mem D X L i⟩ := sorry

/-- A line-bundle class is sent to the relative de Rham exponential of its first Chern class. -/
theorem deRhamApp_lineBundle (D : RationalChernTheory.{u})
    (ch : @ChernClass.ChernCharacter QcqsOverQ _ QcqsOverQ.toScheme
      D.A D.Agrade D.gradedAlgebra D.gradedFirstChernClass D.algebra)
    (X : QcqsOverQ.{u}) (L : X.obj.left.PicardGroup) :
    deRhamApp D ch X (ChernClass.picardK0Class X.obj.left L) =
      deRhamExp D X L := sorry

end AlgebraicGeometry.ChernClass.ChernCharacter
