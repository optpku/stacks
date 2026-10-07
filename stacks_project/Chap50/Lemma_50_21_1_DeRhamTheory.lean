module

public import stacks_project.Chap45.Proposition_45_12_1
public import stacks_project.Chap50.Lemma_50_3_4
public import stacks_project.Chap50.Lemma_50_4_1_CupProduct
public import stacks_project.Chap50.Lemma_50_9_1
public import stacks_project.Chap50.Remark_50_4_3_ClassAction
public import ReasLib.Algebra.Category.ModuleCat.Graded.Colimits
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CanonicalAction

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme is qcqs when its underlying space is quasi-compact and quasi-separated. -/
class IsQcqs (X : Scheme.{u}) : Prop extends CompactSpace X, QuasiSeparatedSpace X

/-- The full subcategory of quasi-compact and quasi-separated schemes. -/
def Qcqs : Type (u + 1) :=
  ObjectProperty.FullSubcategory (fun X : Scheme.{u} ↦ IsQcqs X)

namespace Qcqs

/-- The category structure inherited by the full subcategory of qcqs schemes. -/
instance category : Category.{u} Qcqs.{u} :=
  inferInstanceAs
    (Category.{u} (ObjectProperty.FullSubcategory (fun X : Scheme.{u} ↦ IsQcqs X)))

/-- Regard a scheme with its canonical qcqs properties as an object of `Scheme.Qcqs`. -/
def of (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] : Qcqs.{u} :=
  ⟨X, IsQcqs.mk⟩

/-- The scheme underlying `Qcqs.of X` is `X`. -/
theorem of_obj (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    (of X).obj = X := sorry

/-- Every object of `Scheme.Qcqs` carries its defining qcqs property. -/
instance (X : Qcqs.{u}) : IsQcqs X.obj := X.property

/-- The inclusion of qcqs schemes into all schemes. -/
def toScheme : Qcqs.{u} ⥤ Scheme.{u} :=
  ObjectProperty.ι (fun X : Scheme.{u} ↦ IsQcqs X)

/-- The qcqs inclusion sends an object to its underlying scheme. -/
theorem toScheme_obj (X : Qcqs.{u}) : toScheme.obj X = X.obj := sorry

end Qcqs

namespace DeRham

/-- The canonical structure morphism from a scheme to the universe-lifted model of `Spec ℤ`. -/
noncomputable def absoluteBase (X : Scheme.{u}) :
    X ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
  specULiftZIsTerminal.from X

/-- The binary biproduct presentation used by the explicit absolute de Rham comparison models. -/
noncomputable instance absoluteCoefficientHasBinaryBiproducts (X : Qcqs.{u}) :
    HasBinaryBiproducts
      (RingedSpace.DeRham.coefficientSite
        (absoluteBase X.obj).toLRSHom.toShHom).ModuleCat :=
  Abelian.hasBinaryBiproducts

/-- The graded tensor coproducts for the absolute coefficient-module category. -/
instance absoluteCoefficientGradedHasTensor (X : Qcqs.{u}) :
    ∀ G₁ G₂ : GradedObject ℤ
      (RingedSpace.DeRham.coefficientSite
        (absoluteBase X.obj).toLRSHom.toShHom).ModuleCat,
      GradedObject.HasTensor G₁ G₂ :=
  fun G₁ G₂ j ↦ hasColimitOfHasColimitsOfShape
    (Discrete.functor
      ((((GradedObject.mapBifunctor
        (MonoidalCategory.curriedTensor _) ℤ ℤ).obj G₁).obj G₂).mapObjFun
          (fun x ↦ x.1 + x.2) j))

/-- `absoluteBase X` is the unique morphism from `X` to the chosen model of `Spec ℤ`. -/
theorem absoluteBase_eq (X : Scheme.{u}) :
    absoluteBase X = specULiftZIsTerminal.from X := sorry

/-- A morphism of schemes gives the canonical commutative square between their absolute
structure morphisms. -/
theorem absoluteCommSq {X' X : Scheme.{u}} (f : X' ⟶ X) :
    CommSq f (absoluteBase X') (absoluteBase X) (𝟙 _) := sorry

/-- Absolute de Rham cohomology in even degree `2 * i`. -/
noncomputable abbrev evenCohomology (X : Scheme.{u}) (i : ℕ) : Type u :=
  cohomologyOverAffineBase (absoluteBase X) (2 * (i : ℤ))

/-- The even absolute de Rham group uses cohomological degree `2 * i`. -/
theorem evenCohomology_def (X : Scheme.{u}) (i : ℕ) :
    evenCohomology X i =
      cohomologyOverAffineBase (absoluteBase X) (2 * (i : ℤ)) := sorry

/-- An explicit realization of the abstract Chern-class theory by even absolute de Rham
cohomology on qcqs schemes. The algebra and all comparison maps are data, while their
compatibility conditions are proof fields. -/
structure ChernTheory.{v} where
  /-- The contravariant graded cohomology algebra. -/
  A : Qcqs.{v}ᵒᵖ ⥤ RingCat.{v}
  /-- The nonnegative homogeneous pieces of the cohomology algebra. -/
  Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X))
  /-- The graded-algebra structure on each value of the cohomology theory. -/
  gradedAlgebra : ∀ X, GradedAlgebra (Agrade X)
  /-- The five axioms which construct total Chern classes. -/
  toTheory : @ChernClass.Theory Qcqs _ Qcqs.toScheme A Agrade gradedAlgebra
  /-- Identification of the degree-`i` piece with `H_dR^(2i)(X/ℤ)`. -/
  componentEquiv : ∀ X i, Agrade X i ≃+ evenCohomology X.obj i
  /-- The concrete Chapter 50 constant-one class in degree-zero absolute de Rham cohomology. -/
  cohomologyUnit : ∀ (X : Qcqs.{v}), cohomology (absoluteBase X.obj) 0
  /-- The degree-zero class is the constant-one class constructed from the de Rham complex. -/
  cohomologyUnit_eq : ∀ (X : Qcqs.{v}), cohomologyUnit X =
    ClassAction.cohomologyOneCanonical (absoluteBase X.obj)
  /-- The canonical unit family in even absolute de Rham cohomology. -/
  deRhamUnit : ∀ (X : Qcqs.{v}), ∀ i, evenCohomology X.obj i
  /-- The degree-zero component of the family unit is the concrete cohomology unit. -/
  deRhamUnit_zero : ∀ (X : Qcqs.{v}),
    deRhamUnit X 0 = cohomologyUnit X
  /-- Every positive-degree term of the de Rham unit family vanishes. -/
  deRhamUnit_succ : ∀ (X : Qcqs.{v}) i, deRhamUnit X (i + 1) = 0
  /-- The degreewise Chapter 50 cup-product map before reindexing the even degrees. -/
  cohomologyCupProduct : ∀ (X : Qcqs.{v}) (i j : ℕ),
    MonoidalCategoryStruct.tensorObj
        (cohomology (absoluteBase X.obj) (2 * (i : ℤ)))
        (cohomology (absoluteBase X.obj) (2 * (j : ℤ))) ⟶
      cohomology (absoluteBase X.obj) (2 * (i : ℤ) + 2 * (j : ℤ))
  /-- The displayed product is the wedge-induced Chapter 50 cup product for the stored explicit
  derived tensor model. -/
  cohomologyCupProduct_eq : ∀ (X : Qcqs.{v}) (i j : ℕ),
    cohomologyCupProduct X i j =
      CanonicalAction.cupMorphism (absoluteBase X.obj) (2 * (i : ℤ)) (2 * (j : ℤ))
  /-- The binary even-degree cup product, with the result indexed by the sum degree. -/
  cupProduct : ∀ (X : Qcqs.{v}) {i j n : ℕ}, i + j = n →
    evenCohomology X.obj i → evenCohomology X.obj j → evenCohomology X.obj n
  /-- Reindexing `cohomologyCupProduct` gives the binary even-degree operation. -/
  cupProduct_eq : ∀ (X : Qcqs.{v}) {i j n : ℕ} (h : i + j = n)
      (a : evenCohomology X.obj i) (b : evenCohomology X.obj j),
    HEq (cupProduct X h a b)
      ((cohomologyCupProduct X i j).hom
        (TensorProduct.tmul (coefficientRing (absoluteBase X.obj)) a b))
  /-- Cup-product convolution on families of even absolute de Rham classes. -/
  cupProductConvolution : ∀ (X : Qcqs.{v}),
    (∀ i, evenCohomology X.obj i) → (∀ i, evenCohomology X.obj i) →
      ∀ i, evenCohomology X.obj i
  /-- The family product is the finite convolution of the concrete cup products. -/
  cupProductConvolution_component : ∀ (X : Qcqs.{v})
      (a b : ∀ i, evenCohomology X.obj i) (n : ℕ),
    cupProductConvolution X a b n =
      ∑ k : Fin (n + 1), cupProduct X
        (Nat.add_sub_of_le (Nat.le_of_lt_succ k.isLt)) (a k) (b (n - k))
  /-- Coefficients of the abstract unit lie in their indicated homogeneous pieces. -/
  oneCoeff_mem : ∀ (X : Qcqs.{v}) i,
    PowerSeries.coeff i (1 : PowerSeries (A.obj (Opposite.op X))) ∈ Agrade X i
  /-- The degree equivalences transport the abstract unit to the concrete de Rham unit. -/
  unit_component : ∀ (X : Qcqs.{v}) i,
    componentEquiv X i ⟨PowerSeries.coeff i 1, oneCoeff_mem X i⟩ = deRhamUnit X i
  /-- Products of series with homogeneous coefficients again have homogeneous coefficients. -/
  mulCoeff_mem : ∀ (X : Qcqs.{v}) (a b : PowerSeries (A.obj (Opposite.op X))),
    (∀ i, PowerSeries.coeff i a ∈ Agrade X i) →
    (∀ i, PowerSeries.coeff i b ∈ Agrade X i) →
    ∀ i, PowerSeries.coeff i (a * b) ∈ Agrade X i
  /-- The degree equivalences transport abstract multiplication to de Rham cup convolution. -/
  mul_component : ∀ (X : Qcqs.{v}) (a b : PowerSeries (A.obj (Opposite.op X)))
      (ha : ∀ i, PowerSeries.coeff i a ∈ Agrade X i)
      (hb : ∀ i, PowerSeries.coeff i b ∈ Agrade X i) (n : ℕ),
    componentEquiv X n ⟨PowerSeries.coeff n (a * b), mulCoeff_mem X a b ha hb n⟩ =
      cupProductConvolution X
        (fun i ↦ componentEquiv X i ⟨PowerSeries.coeff i a, ha i⟩)
        (fun i ↦ componentEquiv X i ⟨PowerSeries.coeff i b, hb i⟩) n
  /-- Pullback on the even absolute de Rham groups. -/
  deRhamPullback : ∀ {X' X : Qcqs.{v}}, (X' ⟶ X) → ∀ i,
    evenCohomology X.obj i →+ evenCohomology X'.obj i
  /-- The explicit right-derived comparison used to construct absolute de Rham pullback. -/
  pullbackDerived : ∀ {X' X : Qcqs.{v}} (f : X' ⟶ X),
    Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived
        (Cohomology.coefficientHom (absoluteCommSq (Qcqs.toScheme.map f))))
      (RingedSite.Hom.ModuleQis
        (RingedSpace.DeRham.coefficientSite
          (absoluteBase X'.obj).toLRSHom.toShHom))
  /-- In every even degree, the displayed map is the cohomology map induced from the
  Chapter 50 de Rham-complex pullback comparison. -/
  deRhamPullback_eq : ∀ {X' X : Qcqs.{v}} (f : X' ⟶ X) (i : ℕ)
      (a : evenCohomology X.obj i),
    deRhamPullback f i a =
      (@Cohomology.restrictedPullback _ _ _ _ _ _ _ _
        (absoluteCommSq (Qcqs.toScheme.map f)) (2 * (i : ℤ))
        (pullbackDerived f)).hom a
  /-- The degree equivalences identify algebra pullback with de Rham pullback. -/
  pullback_component : ∀ {X' X : Qcqs.{v}} (f : X' ⟶ X) (i : ℕ)
      (a : Agrade X i),
    deRhamPullback f i (componentEquiv X i a) =
      componentEquiv X' i
        ⟨A.map f.op a, toTheory.pullback_mem f i a⟩
  /-- The Chapter 50 de Rham first-Chern and cup-product context on each absolute scheme. -/
  chernClass : ∀ (X : Qcqs.{v}), ChernClassContext (absoluteBase X.obj)
  /-- The Chapter 50 pullback comparison for the absolute de Rham contexts. -/
  chernPullback : ∀ {X' X : Qcqs.{v}} (f : X' ⟶ X),
    ChernClassContext.Pullback (absoluteCommSq (Qcqs.toScheme.map f))
      (chernClass X) (chernClass X')
  /-- The all-degree pullback specializes in degree one to the Chapter 50 pullback map. -/
  pullback_degree_one : ∀ {X' X : Qcqs.{v}} (f : X' ⟶ X)
      (a : evenCohomology X.obj 1),
    deRhamPullback f 1 a = (chernPullback f).deRhamPullback a
  /-- The abstract and Chapter 50 de Rham first Chern classes agree degreewise. -/
  firstChernClass_component : ∀ (X : Qcqs.{v})
      (L : (Qcqs.toScheme.obj X).PicardGroup),
    componentEquiv X 1 (toTheory.firstChernClass X L) =
      (chernClass X).deRhamFirstChern L
  /-- The series `1 + c₁(L) T` has homogeneous coefficients. -/
  lineBundleCoeff_mem : ∀ (X : Qcqs.{v})
      (L : (Qcqs.toScheme.obj X).PicardGroup) i,
    PowerSeries.coeff i
        (1 + PowerSeries.monomial 1
          (toTheory.firstChernClass X L : A.obj (Opposite.op X))) ∈
      Agrade X i

namespace ChernTheory

/-- Build an absolute de Rham realization from its graded algebra, theory, degree
identifications, concrete de Rham operations, and compatibility laws. -/
def ofTheory := @ChernTheory.mk

/-- The family unit is the transported abstract unit. -/
theorem unit_spec (D : ChernTheory.{u}) (X : Qcqs.{u}) (i : ℕ) :
    D.componentEquiv X i ⟨PowerSeries.coeff i 1, D.oneCoeff_mem X i⟩ =
      D.deRhamUnit X i := sorry

/-- The degree-zero unit is the canonical constant-one de Rham cohomology class. -/
theorem cohomologyUnit_spec (D : ChernTheory.{u}) (X : Qcqs.{u})
    : D.cohomologyUnit X =
      ClassAction.cohomologyOneCanonical (absoluteBase X.obj) := sorry

/-- The cohomology product is the canonical wedge-induced product, independently of the
explicit derived tensor model. -/
theorem cohomologyCupProduct_spec (D : ChernTheory.{u}) (X : Qcqs.{u})
    (i j : ℕ) :
    D.cohomologyCupProduct X i j =
      CanonicalAction.cupMorphism (absoluteBase X.obj) (2 * (i : ℤ)) (2 * (j : ℤ)) := sorry

/-- Abstract multiplication is transported to concrete de Rham cup convolution. -/
theorem multiplication_spec (D : ChernTheory.{u}) (X : Qcqs.{u})
    (a b : PowerSeries (D.A.obj (Opposite.op X)))
    (ha : ∀ i, PowerSeries.coeff i a ∈ D.Agrade X i)
    (hb : ∀ i, PowerSeries.coeff i b ∈ D.Agrade X i) (n : ℕ) :
    D.componentEquiv X n
        ⟨PowerSeries.coeff n (a * b), D.mulCoeff_mem X a b ha hb n⟩ =
      D.cupProductConvolution X
        (fun i ↦ D.componentEquiv X i ⟨PowerSeries.coeff i a, ha i⟩)
        (fun i ↦ D.componentEquiv X i ⟨PowerSeries.coeff i b, hb i⟩) n := sorry

/-- Abstract pullback is transported to absolute de Rham pullback in every even degree. -/
theorem pullback_spec (D : ChernTheory.{u}) {X' X : Qcqs.{u}} (f : X' ⟶ X)
    (i : ℕ) (a : D.Agrade X i) :
    D.deRhamPullback f i (D.componentEquiv X i a) =
      D.componentEquiv X' i
        ⟨D.A.map f.op a,
          @ChernClass.Theory.pullback_mem _ _ Qcqs.toScheme D.A D.Agrade
            D.gradedAlgebra D.toTheory X' X f i a⟩ := sorry

/-- The all-degree pullback is the map induced by the canonical de Rham-complex comparison. -/
theorem deRhamPullback_spec (D : ChernTheory.{u}) {X' X : Qcqs.{u}} (f : X' ⟶ X)
    (i : ℕ) (a : evenCohomology X.obj i) :
    D.deRhamPullback f i a =
      (@Cohomology.restrictedPullback _ _ _ _ _ _ _ _
        (absoluteCommSq (Qcqs.toScheme.map f)) (2 * (i : ℤ))
        (D.pullbackDerived f)).hom a := sorry

/-- The absolute de Rham unit does not depend on the explicit realization model. -/
theorem cohomologyUnit_eq_of_theories (D D' : ChernTheory.{u}) (X : Qcqs.{u}) :
    D.cohomologyUnit X = D'.cohomologyUnit X := sorry

/-- The unit family is independent of the explicit realization model. -/
theorem deRhamUnit_eq_of_theories (D D' : ChernTheory.{u}) (X : Qcqs.{u}) :
    D.deRhamUnit X = D'.deRhamUnit X := sorry

/-- The even-degree cup product does not depend on the explicit realization model. -/
theorem cupProduct_eq_of_theories (D D' : ChernTheory.{u}) (X : Qcqs.{u})
    {i j n : ℕ} (h : i + j = n) (a : evenCohomology X.obj i)
    (b : evenCohomology X.obj j) :
    D.cupProduct X h a b = D'.cupProduct X h a b := sorry

/-- Cup-product convolution on even cohomology families is independent of the realization
model. -/
theorem cupProductConvolution_eq_of_theories (D D' : ChernTheory.{u})
    (X : Qcqs.{u}) (a b : ∀ i, evenCohomology X.obj i) :
    D.cupProductConvolution X a b = D'.cupProductConvolution X a b := sorry

/-- Absolute de Rham pullback does not depend on the explicit comparison model. -/
theorem deRhamPullback_eq_of_theories (D D' : ChernTheory.{u})
    {X' X : Qcqs.{u}} (f : X' ⟶ X) (i : ℕ) :
    D.deRhamPullback f i = D'.deRhamPullback f i := sorry

/-- The transported abstract first Chern class is the Chapter 50 de Rham first Chern class. -/
theorem firstChernClass_spec (D : ChernTheory.{u}) (X : Qcqs.{u})
    (L : X.obj.PicardGroup) :
    D.componentEquiv X 1
        (@ChernClass.Theory.firstChernClass _ _ Qcqs.toScheme D.A D.Agrade
          D.gradedAlgebra D.toTheory X L) =
      (D.chernClass X).deRhamFirstChern L := sorry

/-- The graded first Chern class carried by an absolute de Rham Chern theory. -/
def gradedFirstChernClass (D : ChernTheory.{u}) :
    ∀ X, (Qcqs.toScheme.obj X).PicardGroup →+ D.Agrade X 1 :=
  @ChernClass.Theory.firstChernClass _ _ Qcqs.toScheme D.A D.Agrade
    D.gradedAlgebra D.toTheory

/-- `gradedFirstChernClass` is the first Chern class stored in the underlying theory. -/
theorem gradedFirstChernClass_apply (D : ChernTheory.{u}) (X : Qcqs.{u})
    (L : (Qcqs.toScheme.obj X).PicardGroup) :
    D.gradedFirstChernClass X L =
      @ChernClass.Theory.firstChernClass _ _ Qcqs.toScheme D.A D.Agrade
        D.gradedAlgebra D.toTheory X L := sorry

end ChernTheory

end DeRham

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ChernClass.TotalChernClass

open Scheme Scheme.DeRham

/-- Transport a power series with homogeneous coefficients to its family of even absolute
de Rham cohomology classes. -/
def seriesToDeRham (D : ChernTheory.{u}) (X : Scheme.Qcqs.{u})
    (a : PowerSeries (D.A.obj (Opposite.op X)))
    (ha : ∀ i, PowerSeries.coeff i a ∈ D.Agrade X i) :
    ∀ i, evenCohomology X.obj i :=
  fun i ↦ D.componentEquiv X i ⟨PowerSeries.coeff i a, ha i⟩

/-- Evaluation of `seriesToDeRham` is coefficientwise transport through
`ChernTheory.componentEquiv`. -/
theorem seriesToDeRham_apply (D : ChernTheory.{u}) (X : Scheme.Qcqs.{u})
    (a : PowerSeries (D.A.obj (Opposite.op X)))
    (ha : ∀ i, PowerSeries.coeff i a ∈ D.Agrade X i) (i : ℕ) :
    seriesToDeRham D X a ha i =
      D.componentEquiv X i ⟨PowerSeries.coeff i a, ha i⟩ := sorry

/-- The family of even absolute de Rham classes underlying a total Chern class. -/
def deRhamApp (D : ChernTheory.{u})
    (c : ChernClass.TotalChernClass Scheme.Qcqs.toScheme D.A D.Agrade
      D.gradedFirstChernClass)
    (X : Scheme.Qcqs.{u}) (alpha : Scheme.VectorBundleK0 X.obj) :
    ∀ i, evenCohomology X.obj i :=
  seriesToDeRham D X (c.app X alpha) (c.coeff_mem X alpha)

/-- The `i`-th de Rham component is the transported `i`-th power-series coefficient. -/
theorem deRhamApp_apply (D : ChernTheory.{u})
    (c : ChernClass.TotalChernClass Scheme.Qcqs.toScheme D.A D.Agrade
      D.gradedFirstChernClass)
    (X : Scheme.Qcqs.{u}) (alpha : Scheme.VectorBundleK0 X.obj) (i : ℕ) :
    deRhamApp D c X alpha i =
      D.componentEquiv X i
        ⟨PowerSeries.coeff i (c.app X alpha), c.coeff_mem X alpha i⟩ := sorry

/-- Addition in vector-bundle `K₀` becomes multiplication of the representing homogeneous
power series, hence cup-product convolution after the de Rham identifications. -/
theorem deRhamApp_add (D : ChernTheory.{u})
    (c : ChernClass.TotalChernClass Scheme.Qcqs.toScheme D.A D.Agrade
      D.gradedFirstChernClass)
    (X : Scheme.Qcqs.{u}) (alpha beta : Scheme.VectorBundleK0 X.obj) :
    deRhamApp D c X (alpha + beta) =
      D.cupProductConvolution X (deRhamApp D c X alpha) (deRhamApp D c X beta) := sorry

/-- Pullback of vector-bundle classes agrees degreewise with pullback in absolute de Rham
cohomology. -/
theorem deRhamApp_naturality (D : ChernTheory.{u})
    (c : ChernClass.TotalChernClass Scheme.Qcqs.toScheme D.A D.Agrade
      D.gradedFirstChernClass)
    {X' X : Scheme.Qcqs.{u}} (f : X' ⟶ X)
    (alpha : Scheme.VectorBundleK0 X.obj) (i : ℕ) :
    D.deRhamPullback f i (deRhamApp D c X alpha i) =
      deRhamApp D c X'
        (Scheme.VectorBundleK0.pullback (Scheme.Qcqs.toScheme.map f) alpha) i := sorry

/-- The concrete de Rham family `1 + c₁ᵈᴿ(L)`, with the unit in degree zero, the first Chern
class in degree one, and zero in every higher degree. -/
def lineBundleValue (D : ChernTheory.{u}) (X : Scheme.Qcqs.{u})
    (L : X.obj.PicardGroup) : ∀ i, evenCohomology X.obj i :=
  fun
  | 0 => D.deRhamUnit X 0
  | 1 => D.deRhamUnit X 1 +
      D.componentEquiv X 1
        (@ChernClass.Theory.firstChernClass _ _ Scheme.Qcqs.toScheme D.A D.Agrade
          D.gradedAlgebra D.toTheory X L)
  | n + 2 => D.deRhamUnit X (n + 2)

/-- The degree-zero component of `lineBundleValue` is the canonical de Rham unit. -/
theorem lineBundleValue_zero (D : ChernTheory.{u}) (X : Scheme.Qcqs.{u})
    (L : X.obj.PicardGroup) :
    lineBundleValue D X L 0 = D.cohomologyUnit X := sorry

/-- The degree-one component of `lineBundleValue` is the de Rham first Chern class. -/
theorem lineBundleValue_one (D : ChernTheory.{u}) (X : Scheme.Qcqs.{u})
    (L : X.obj.PicardGroup) :
    lineBundleValue D X L 1 = (D.chernClass X).deRhamFirstChern L := sorry

/-- Every component of `lineBundleValue` above degree one vanishes. -/
theorem lineBundleValue_succ_succ (D : ChernTheory.{u}) (X : Scheme.Qcqs.{u})
    (L : X.obj.PicardGroup) (n : ℕ) :
    lineBundleValue D X L (n + 2) = 0 := sorry

/-- On a line bundle, the total de Rham Chern class is `1 + c₁ᵈᴿ`. -/
theorem deRhamApp_lineBundle (D : ChernTheory.{u})
    (c : ChernClass.TotalChernClass Scheme.Qcqs.toScheme D.A D.Agrade
      D.gradedFirstChernClass)
    (X : Scheme.Qcqs.{u}) (L : X.obj.PicardGroup) :
    deRhamApp D c X (ChernClass.picardK0Class X.obj L) =
      lineBundleValue D X L := sorry

/-- A product-valued total de Rham Chern-class rule. This is the concrete family view of the
canonical `ChernClass.TotalChernClass`, not a competing graded-ring owner. -/
structure DeRhamRule (D : ChernTheory.{u}) where
  /-- The family of even absolute de Rham classes assigned to a vector-bundle `K₀`-class. -/
  app : ∀ X : Scheme.Qcqs.{u}, Scheme.VectorBundleK0 X.obj →
    ∀ i, evenCohomology X.obj i
  /-- Addition in vector-bundle `K₀` becomes de Rham cup-product convolution. -/
  map_add : ∀ (X : Scheme.Qcqs.{u}) (alpha beta : Scheme.VectorBundleK0 X.obj) (i : ℕ),
    app X (alpha + beta) i =
      D.cupProductConvolution X (app X alpha) (app X beta) i
  /-- The zero vector-bundle class has the de Rham unit family as total class. -/
  map_zero : ∀ (X : Scheme.Qcqs.{u}) (i : ℕ), app X 0 i = D.deRhamUnit X i
  /-- The rule commutes degreewise with the concrete absolute de Rham pullback. -/
  naturality : ∀ {X' X : Scheme.Qcqs.{u}} (f : X' ⟶ X)
      (alpha : Scheme.VectorBundleK0 X.obj) (i : ℕ),
    D.deRhamPullback f i (app X alpha i) =
      app X' (Scheme.VectorBundleK0.pullback (Scheme.Qcqs.toScheme.map f) alpha) i
  /-- A line bundle has total class equal to the actual family `1 + c₁ᵈᴿ`. -/
  lineBundle : ∀ (X : Scheme.Qcqs.{u}) (L : X.obj.PicardGroup) (i : ℕ),
    app X (ChernClass.picardK0Class X.obj L) i = lineBundleValue D X L i

namespace DeRhamRule

/-- Take the concrete family-valued view of an abstract total Chern class. -/
def ofTotalChernClass (D : ChernTheory.{u})
    (c : ChernClass.TotalChernClass Scheme.Qcqs.toScheme D.A D.Agrade
      D.gradedFirstChernClass) : DeRhamRule D where
  app := deRhamApp D c
  map_add := sorry
  map_zero := sorry
  naturality := sorry
  lineBundle := sorry

/-- Evaluation of the concrete view is the transported coefficient family `deRhamApp`. -/
theorem ofTotalChernClass_app (D : ChernTheory.{u})
    (c : ChernClass.TotalChernClass Scheme.Qcqs.toScheme D.A D.Agrade
      D.gradedFirstChernClass)
    (X : Scheme.Qcqs.{u}) (alpha : Scheme.VectorBundleK0 X.obj) :
    (ofTotalChernClass D c).app X alpha = deRhamApp D c X alpha := sorry

/-- The concrete de Rham family view remembers the underlying abstract total Chern class. -/
theorem ofTotalChernClass_injective (D : ChernTheory.{u}) :
    Function.Injective (ofTotalChernClass D) := sorry

/-- Every concrete de Rham rule is represented by an abstract total Chern class. -/
theorem ofTotalChernClass_surjective (D : ChernTheory.{u}) :
    Function.Surjective (ofTotalChernClass D) := sorry

/-- The family-valued total de Rham Chern rule is independent of the explicit graded-ring,
tensor, and comparison presentation used to construct it. -/
theorem app_eq_of_theories (D D' : ChernTheory.{u})
    (c : DeRhamRule D) (c' : DeRhamRule D') : c.app = c'.app := sorry

end DeRhamRule

end AlgebraicGeometry.ChernClass.TotalChernClass
