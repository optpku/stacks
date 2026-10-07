module

public import stacks_project.Chap45.Proposition_45_14_17
public import stacks_project.Chap50.Lemma_50_21_1_DeRhamTheory
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CanonicalAction
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators TensorProduct

noncomputable section

universe u y z

namespace AlgebraicGeometry.Scheme.DeRham

variable {k : Type u} [Field k] [CharZero k]
variable {V : Type (u + 1)} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
variable {pointCycle : CHgrade point 0}
variable {geometry : WeilCohomology.SmoothProjectiveContext k V dimension product fst snd
  point CH CHgrade cyclePullback cyclePushforward pointCycle}
variable {H : V → Type (u + 1)} [∀ X, Ring (H X)] [∀ X, Algebra k (H X)]

/-- Coefficient modules for a represented scheme have their canonical binary biproducts. -/
noncomputable instance realizationCoefficientHasBinaryBiproducts (X : V) :
    HasBinaryBiproducts
      (RingedSpace.DeRham.coefficientSite
        (geometry.scheme.obj X).hom.toLRSHom.toShHom).ModuleCat :=
  Abelian.hasBinaryBiproducts

/-- Graded coefficient modules for a represented scheme have their canonical tensor
coproducts. -/
instance realizationCoefficientGradedHasTensor (X : V) :
    ∀ G₁ G₂ : GradedObject ℤ
      (RingedSpace.DeRham.coefficientSite
        (geometry.scheme.obj X).hom.toLRSHom.toShHom).ModuleCat,
      GradedObject.HasTensor G₁ G₂ :=
  fun G₁ G₂ j ↦ hasColimitOfHasColimitsOfShape
    (Discrete.functor
      ((((GradedObject.mapBifunctor
        (MonoidalCategory.curriedTensor _) ℤ ℤ).obj G₁).obj G₂).mapObjFun
          (fun x ↦ x.1 + x.2) j))

/-- Explicit model choices for the total graded de Rham algebra on a presentation of
smooth projective `k`-schemes. The structure stores the concrete geometric and
cohomological data used to assemble a pre-Weil theory, together with specifications
identifying them with the canonical Chapter 50 de Rham constructions. It does not
assume axiom (A8) or the desired Weil conclusion. -/
structure PreWeilRealization.{uR, yR, zR}
    {k : Type uR} [Field k] [CharZero k]
    {V : Type (uR + 1)} [Category.{zR} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type yR} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    (geometry : WeilCohomology.SmoothProjectiveContext k V dimension product fst snd
      point CH CHgrade cyclePullback cyclePushforward pointCycle)
    (H : V → Type (uR + 1)) [∀ X, Ring (H X)] [∀ X, Algebra k (H X)] where
  /-- Data (D0): the chosen Tate line is one-dimensional. -/
  tateLine_rank : Module.finrank k (ULift.{uR + 1} k) = 1
  /-- The cohomological-degree and Tate-twist summands of total de Rham cohomology. -/
  Hgrade : ∀ X, ℤ × ℤ → Submodule k (H X)
  /-- The bidegree summands exhaust total de Rham cohomology. -/
  Hgrade_isInternal : ∀ X, DirectSum.IsInternal (Hgrade X)
  /-- Tensoring with the Tate line raises the twist index by one. -/
  tateTwist : ∀ X i j,
    Hgrade X (i, j) ⊗[k] (ULift.{uR + 1} k) ≃ₗ[k] Hgrade X (i, j + 1)
  /-- The de Rham unit has bidegree `(0, 0)`. -/
  one_mem : ∀ X, (1 : H X) ∈ Hgrade X (0, 0)
  /-- Cup product adds cohomological degrees and Tate twists. -/
  mul_mem : ∀ X {p q : ℤ × ℤ} (a : Hgrade X p) (b : Hgrade X q),
    (a : H X) * b ∈ Hgrade X (p + q)
  /-- Homogeneous de Rham cup products are graded-commutative. -/
  gradedComm : ∀ X {i i' j j' : ℤ} (a : Hgrade X (i, j))
      (b : Hgrade X (i', j')),
    (a : H X) * b = (-1 : H X) ^ (i * i').natAbs * ((b : H X) * a)
  /-- Contravariant pullback on total de Rham cohomology. -/
  pullback : ∀ {X Y : V}, (X ⟶ Y) → H Y →ₐ[k] H X
  /-- Pullback preserves both de Rham bidegrees. -/
  pullback_mem : ∀ {X Y : V} (f : X ⟶ Y) (p : ℤ × ℤ) (a : Hgrade Y p),
    pullback f a ∈ Hgrade X p
  /-- De Rham pullback by an identity is the identity. -/
  pullback_id : ∀ X, pullback (𝟙 X) = AlgHom.id k (H X)
  /-- De Rham pullback reverses composition. -/
  pullback_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
    pullback (f ≫ g) = (pullback f).comp (pullback g)
  /-- The first Chern class on the canonical Picard group. -/
  firstChernClass : ∀ X,
    (geometry.scheme.obj X).left.PicardGroup →+ Hgrade X (2, 1)
  /-- Every bidegree is the corresponding relative de Rham cohomology group. -/
  componentEquiv : ∀ X i j,
    Hgrade X (i, j) ≃ₗ[k]
      cohomologyOverAffineBase (geometry.scheme.obj X).hom i
  /-- The square over `Spec k` used by the canonical de Rham pullback. -/
  baseSquare : ∀ {X Y : V} (f : X ⟶ Y),
    CommSq (geometry.scheme.map f).left (geometry.scheme.obj X).hom
      (geometry.scheme.obj Y).hom (𝟙 _)
  /-- The explicit right-derived comparison used by de Rham pullback. -/
  pullbackDerived : ∀ {X Y : V} (f : X ⟶ Y),
    Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived
        (Cohomology.coefficientHom (baseSquare f)))
      (RingedSite.Hom.ModuleQis
        (RingedSpace.DeRham.coefficientSite
          (geometry.scheme.obj X).hom.toLRSHom.toShHom))
  /-- Abstract pullback is the canonical Chapter 50 de Rham pullback in every degree. -/
  pullback_component : ∀ {X Y : V} (f : X ⟶ Y) (i j : ℤ)
      (a : Hgrade Y (i, j)),
    componentEquiv X i j ⟨pullback f a, pullback_mem f (i, j) a⟩ =
      (@Cohomology.restrictedPullback _ _ _ _ _ _ _ _ (baseSquare f) i
        (pullbackDerived f)).hom (componentEquiv Y i j a)
  /-- The abstract unit maps to the canonical constant-one de Rham class. -/
  unit_component : ∀ X,
    componentEquiv X 0 0 ⟨1, one_mem X⟩ =
      ClassAction.cohomologyOneCanonical (geometry.scheme.obj X).hom
  /-- Abstract multiplication is the canonical wedge-induced de Rham cup product. -/
  cupProduct_component : ∀ X i i' j j'
      (a : Hgrade X (i, j))
      (b : Hgrade X (i', j')),
    componentEquiv X (i + i') (j + j')
        ⟨(a : H X) * b, mul_mem X a b⟩ =
      (CanonicalAction.cupMorphism (geometry.scheme.obj X).hom i i').hom
          (TensorProduct.tmul (coefficientRing (geometry.scheme.obj X).hom)
            (componentEquiv X i j a) (componentEquiv X i' j' b))
  /-- The Chapter 50 de Rham first-Chern context on every represented scheme. -/
  chernClass : ∀ X, ChernClassContext (geometry.scheme.obj X).hom
  /-- The abstract and canonical de Rham first Chern classes agree. -/
  firstChernClass_component : ∀ X (L : (geometry.scheme.obj X).left.PicardGroup),
    componentEquiv X 2 1 (firstChernClass X L) =
      (chernClass X).deRhamFirstChern L
  /-- The predicate for represented schemes that are nonempty equidimensional of dimension `d`. -/
  IsNonemptyEquidimensional : V → ℕ → Prop
  /-- The nonempty-equidimensional predicate has its canonical geometric meaning. -/
  nonemptyEquidimensional_iff : ∀ {X d}, IsNonemptyEquidimensional X d ↔
    Nonempty (geometry.scheme.obj X).left ∧
      EquidimensionalSpace (geometry.scheme.obj X).left ∧ dimension X = d
  /-- Every smooth projective scheme over `k` is represented by the chosen domain. -/
  scheme_essentiallySurjective : ∀ (S : SchemeOverField k)
    [Smooth S.hom] [Projective S.hom], ∃ X : V, Nonempty (geometry.scheme.obj X ≅ S)
  /-- Products preserve nonempty equidimensionality and add dimensions. -/
  product_isNonemptyEquidimensional : ∀ {X Y d e},
    IsNonemptyEquidimensional X d → IsNonemptyEquidimensional Y e →
      IsNonemptyEquidimensional (product X Y) (d + e)
  /-- A chosen presentation of binary geometric disjoint unions. -/
  coproduct : V → V → V
  /-- The left inclusion into a represented disjoint union. -/
  inl : ∀ X Y, X ⟶ coproduct X Y
  /-- The right inclusion into a represented disjoint union. -/
  inr : ∀ X Y, Y ⟶ coproduct X Y
  /-- The represented coproduct satisfies the universal property of geometric disjoint union. -/
  schemeCoproduct : ∀ X Y (S : SchemeOverField k), Function.Bijective
    (fun f : geometry.scheme.obj (coproduct X Y) ⟶ S ↦
      (geometry.scheme.map (inl X Y) ≫ f, geometry.scheme.map (inr X Y) ≫ f))
  /-- The predicate for a represented scheme to have empty underlying space. -/
  IsGeometricallyEmpty : V → Prop
  /-- The empty predicate agrees with geometric emptiness. -/
  isEmpty_iff : ∀ X,
    IsGeometricallyEmpty X ↔ IsEmpty (geometry.scheme.obj X).left
  /-- Relative de Rham cohomology of a represented empty scheme vanishes. -/
  emptyCohomology : ∀ {X}, IsGeometricallyEmpty X → ∀ a : H X, a = 0
  /-- Relative de Rham cohomology carries represented disjoint unions to products. -/
  coproductCohomology : ∀ X Y, Function.Bijective
    (fun a : H (coproduct X Y) ↦
      (pullback (inl X Y) a, pullback (inr X Y) a))
  /-- Pullback on the canonical Picard groups of represented schemes. -/
  picardPullback : ∀ {X Y : V}, (X ⟶ Y) →
    (geometry.scheme.obj Y).left.PicardGroup →+ (geometry.scheme.obj X).left.PicardGroup
  /-- The chosen Picard pullback is the canonical pullback of invertible sheaves. -/
  picardPullback_eq : ∀ {X Y : V} (f : X ⟶ Y),
    picardPullback f = Scheme.Hom.picardPullback (geometry.scheme.map f).left
  /-- Canonical Picard pullback is compatible with the de Rham first Chern class. -/
  firstChernClass_naturality : ∀ {X Y : V} (f : X ⟶ Y)
      (L : (geometry.scheme.obj Y).left.PicardGroup),
    pullback f (firstChernClass Y L) =
      firstChernClass X (picardPullback f L)
  /-- The predicate that a represented morphism is a projective bundle of rank `n`. -/
  IsProjectiveBundle : ∀ {P X : V}, (P ⟶ X) → ℕ → Prop
  /-- The projective-bundle predicate records exactly a finite locally free module and
  its canonical geometric projective-bundle representation. -/
  isProjectiveBundle_iff : ∀ {P X : V} (p : P ⟶ X) (n : ℕ),
    IsProjectiveBundle p n ↔ ∃ E : (geometry.scheme.obj X).left.Modules,
      Scheme.Modules.IsFiniteLocallyFreeOfRank n E ∧
        Nonempty (Scheme.ProjectiveBundle.Representation (geometry.scheme.map p).left E)
  /-- The finite locally free module represented by the chosen projective bundle. -/
  projectiveBundleModule : ∀ {P X : V} (p : P ⟶ X) (n : ℕ),
    IsProjectiveBundle p n → (geometry.scheme.obj X).left.Modules
  /-- The chosen projective-bundle module has the stated rank. -/
  projectiveBundleModule_rank : ∀ {P X : V} (p : P ⟶ X) (n : ℕ)
      (hp : IsProjectiveBundle p n),
    Scheme.Modules.IsFiniteLocallyFreeOfRank n (projectiveBundleModule p n hp)
  /-- The represented morphism is the projective bundle of the chosen module. -/
  projectiveBundle_representation : ∀ {P X : V} (p : P ⟶ X) (n : ℕ)
      (hp : IsProjectiveBundle p n),
    Scheme.ProjectiveBundle.Representation (geometry.scheme.map p).left
      (projectiveBundleModule p n hp)
  /-- The tautological Picard class on a represented projective bundle. -/
  projectiveBundleLineBundle : ∀ {P X : V} (p : P ⟶ X) (n : ℕ),
    IsProjectiveBundle p n → (geometry.scheme.obj P).left.PicardGroup
  /-- The chosen Picard class is the canonical tautological projective-bundle class. -/
  projectiveBundleLineBundle_eq : ∀ {P X : V} (p : P ⟶ X) (n : ℕ)
      (hp : IsProjectiveBundle p n),
    projectiveBundleLineBundle p n hp =
      ChernClass.tautologicalPicardClass (geometry.scheme.map p).left
        (projectiveBundleModule p n hp) (projectiveBundle_representation p n hp)
  /-- The explicit de Rham projective-bundle map in each bidegree. -/
  projectiveBundleMap : ∀ {P X : V} (p : P ⟶ X) (n : ℕ),
    IsProjectiveBundle p n → (i j : ℤ) →
      (∀ r : Fin n,
        Hgrade X (i - 2 * ((r : ℕ) : ℤ), j - ((r : ℕ) : ℤ))) →ₗ[k]
          Hgrade P (i, j)
  /-- The projective-bundle map is the canonical sum of pullbacks times powers of
  the tautological de Rham first Chern class. -/
  projectiveBundleMap_apply : ∀ {P X : V} (p : P ⟶ X) (n : ℕ)
      (hp : IsProjectiveBundle p n) (i j : ℤ)
      (a : ∀ r : Fin n,
        Hgrade X (i - 2 * ((r : ℕ) : ℤ), j - ((r : ℕ) : ℤ))),
    (projectiveBundleMap p n hp i j a : H P) =
      ∑ r : Fin n, pullback p (a r) *
        (firstChernClass P (projectiveBundleLineBundle p n hp) : H P) ^
          (r : ℕ)
  /-- The de Rham projective-bundle map is an isomorphism in every bidegree. -/
  projectiveBundleMap_bijective : ∀ {P X : V} (p : P ⟶ X) (n : ℕ)
      (hp : IsProjectiveBundle p n) (i j : ℤ),
    Function.Bijective (projectiveBundleMap p n hp i j)
  /-- The predicate that a represented morphism is an effective Cartier divisor. -/
  IsEffectiveCartierDivisor : ∀ {Y X : V}, (Y ⟶ X) → Prop
  /-- The divisor predicate agrees with the canonical geometric predicate. -/
  isEffectiveCartierDivisor_iff : ∀ {Y X : V} (i : Y ⟶ X),
    IsEffectiveCartierDivisor i ↔
      AlgebraicGeometry.IsEffectiveCartierDivisor (geometry.scheme.map i).left
  /-- The Picard class associated with a represented effective Cartier divisor. -/
  cartierLineBundle : ∀ {Y X : V} (i : Y ⟶ X),
    IsEffectiveCartierDivisor i → (geometry.scheme.obj X).left.PicardGroup
  /-- The chosen Cartier-divisor line bundle is the canonical associated Picard class. -/
  cartierLineBundle_eq : ∀ {Y X : V} (i : Y ⟶ X)
      (hi : IsEffectiveCartierDivisor i),
    cartierLineBundle i hi =
      @Scheme.Modules.picardClass (geometry.scheme.obj X).left
        (@Scheme.effectiveCartierDivisorAssociatedSheaf (geometry.scheme.obj X).left
          inferInstance (RingedSpace.Hom.idealSheafSubobject
            (geometry.scheme.map i).left.toShHom)
          ⟨Scheme.Modules.Invertible.tensorRight_isEquivalence
            ((isEffectiveCartierDivisor_iff i).mp hi).invertibleIdealSheaf⟩)
        (@Scheme.effectiveCartierDivisorAssociatedSheaf_isInvertible
          (geometry.scheme.obj X).left inferInstance
          (RingedSpace.Hom.idealSheafSubobject (geometry.scheme.map i).left.toShHom)
          ⟨Scheme.Modules.Invertible.tensorRight_isEquivalence
            ((isEffectiveCartierDivisor_iff i).mp hi).invertibleIdealSheaf⟩)
  /-- A de Rham class vanishing on a divisor is annihilated by its canonical class. -/
  effectiveCartierDivisor_vanishing : ∀ {Y X : V} (i : Y ⟶ X)
      (hi : IsEffectiveCartierDivisor i) (a : H X),
    pullback i a = 0 →
      a * firstChernClass X (cartierLineBundle i hi) = 0
  /-- The canonical scalar map into bidegree `(0, 0)` cohomology of the point. -/
  pointH0Map : k →ₗ[k] Hgrade point (0, 0)
  /-- The point map is induced by the algebra structure on total de Rham cohomology. -/
  pointH0Map_apply : ∀ a : k,
    (pointH0Map a : H point) = algebraMap k (H point) a
  /-- The point map is a linear equivalence. -/
  pointH0Map_bijective : Function.Bijective pointH0Map
  /-- The canonical exterior product determined by de Rham pullback and cup product. -/
  kunnethMap : ∀ X Y, H X ⊗[k] H Y →ₗ[k] H (product X Y)
  /-- The exterior product sends a pure tensor to the cup product of its pullbacks. -/
  kunnethMap_tmul : ∀ {X Y : V} (a : H X) (b : H Y),
    kunnethMap X Y (a ⊗ₜ[k] b) = pullback (fst X Y) a * pullback (snd X Y) b
  /-- The canonical de Rham exterior-product map preserves bidegrees. -/
  kunnethMap_mem : ∀ {X Y : V} {p q : ℤ × ℤ}
      (a : Hgrade X p) (b : Hgrade Y q),
    kunnethMap X Y (a ⊗ₜ[k] b) ∈ Hgrade (product X Y) (p + q)
  /-- The canonical de Rham exterior-product map is an isomorphism. -/
  kunnethMap_bijective : ∀ X Y, Function.Bijective (kunnethMap X Y)
  /-- The de Rham cycle-class homomorphism on the canonical Chow rings. -/
  cycleClass : ∀ X, CH X →+* H X
  /-- A codimension-`i` cycle maps to bidegree `(2 * i, i)`. -/
  cycleClass_mem : ∀ X (i : ℤ) (z : CHgrade X i),
    cycleClass X z ∈ Hgrade X (2 * i, i)
  /-- De Rham cycle classes commute with canonical Chow pullback. -/
  cycleClass_pullback : ∀ {X Y : V} (f : X ⟶ Y) (z : CH Y),
    cycleClass X (cyclePullback f z) = pullback f (cycleClass Y z)
  /-- On an effective Cartier divisor, the cycle class is its de Rham first Chern class. -/
  cycleClass_cartier : ∀ {Y X : V} (i : Y ⟶ X)
      (hi : IsEffectiveCartierDivisor i) (z : CHgrade X 1),
    (z : CH X) = cyclePushforward i (1 : CHgrade Y 0) →
      cycleClass X z = firstChernClass X (cartierLineBundle i hi)
  /-- A chosen represented diagonal for every nonempty equidimensional scheme. -/
  diagonal : ∀ {X d}, IsNonemptyEquidimensional X d → (X ⟶ product X X)
  /-- The chosen diagonal represents the canonical geometric diagonal. -/
  diagonal_spec : ∀ {X d} (hX : IsNonemptyEquidimensional X d),
    geometry.scheme.map (diagonal hX) ≫ (geometry.schemeProduct X X).hom =
      Limits.prod.lift (𝟙 _) (𝟙 _)
  /-- The canonical Chow class of the represented diagonal. -/
  diagonalCycle : ∀ {X d}, IsNonemptyEquidimensional X d →
    CHgrade (product X X) d
  /-- The chosen diagonal class is the pushforward of the fundamental class. -/
  diagonalCycle_spec : ∀ {X d} (hX : IsNonemptyEquidimensional X d),
    (diagonalCycle hX : CH (product X X)) =
      cyclePushforward (diagonal hX) (1 : CHgrade X 0)
  /-- De Rham cycle classes carry product diagonals to exterior products. -/
  diagonalCycle_product : ∀ {X Y d e}
      (hX : IsNonemptyEquidimensional X d)
      (hY : IsNonemptyEquidimensional Y e),
    cycleClass (product (product X Y) (product X Y))
        (diagonalCycle (product_isNonemptyEquidimensional hX hY)) =
      kunnethMap (product X Y) (product X Y)
        (TensorProduct.map (kunnethMap X Y) (kunnethMap X Y)
          ((WeilCohomology.tensorInterchange k (H X) (H Y)).symm
            ((LinearEquiv.ofBijective (kunnethMap X X)
                (kunnethMap_bijective X X)).symm
                (cycleClass (product X X) (diagonalCycle hX)) ⊗ₜ[k]
              (LinearEquiv.ofBijective (kunnethMap Y Y)
                (kunnethMap_bijective Y Y)).symm
                (cycleClass (product Y Y) (diagonalCycle hY)))))
  /-- The canonical de Rham trace on a nonempty equidimensional scheme. -/
  integral : ∀ {X d}, IsNonemptyEquidimensional X d → H X →ₗ[k] k
  /-- The trace is normalized by every canonical represented diagonal cycle. -/
  integral_spec : ∀ {X d} (hX : IsNonemptyEquidimensional X d),
    (∀ p : ℤ × ℤ, p ≠ (2 * (dimension X : ℤ), (dimension X : ℤ)) →
        ∀ a : Hgrade X p, integral hX a = 0) ∧
      ∀ (delta : X ⟶ product X X),
        geometry.scheme.map delta ≫ (geometry.schemeProduct X X).hom =
          Limits.prod.lift (𝟙 _) (𝟙 _) →
        ∀ (z : CHgrade (product X X) (dimension X)),
          (z : CH (product X X)) = cyclePushforward delta (1 : CHgrade X 0) →
            ∃ diagonalTensor : H X ⊗[k] H X,
              kunnethMap X X diagonalTensor = cycleClass (product X X) z ∧
                WeilCohomology.contractRight (integral hX) diagonalTensor = 1
  /-- The total trace vanishes away from top bidegree. -/
  integral_vanishes : ∀ {X d} (hX : IsNonemptyEquidimensional X d)
      (p : ℤ × ℤ), p ≠ (2 * (d : ℤ), (d : ℤ)) →
    ∀ a : Hgrade X p, integral hX a = 0
  /-- Contracting the canonical diagonal class by the de Rham trace gives the unit. -/
  integral_diagonal : ∀ {X d} (hX : IsNonemptyEquidimensional X d),
    WeilCohomology.contractRight (integral hX)
        ((LinearEquiv.ofBijective (kunnethMap X X)
          (kunnethMap_bijective X X)).symm
          (cycleClass (product X X) (diagonalCycle hX))) = 1
  /-- The predicate that a represented morphism is the blowup of a smooth center. -/
  IsBlowupOfSmoothCenter : ∀ {X' X : V}, (X' ⟶ X) → Prop
  /-- The blowup predicate has its canonical geometric meaning. -/
  isBlowupOfSmoothCenter_iff : ∀ {X' X : V} (b : X' ⟶ X),
    IsBlowupOfSmoothCenter b ↔
      ∃ I : (geometry.scheme.obj X).left.IdealSheafData,
        Smooth (I.subschemeι ≫ (geometry.scheme.obj X).hom) ∧
          IsBlowup (geometry.scheme.map b).left I
  /-- Pullback along a represented blowup in a smooth center is injective. -/
  blowupPullback_injective : ∀ {X' X : V} (b : X' ⟶ X),
    IsBlowupOfSmoothCenter b → Function.Injective (pullback b)

namespace PreWeilRealization

/-- Canonical divisor vanishing implies axiom (A4) for the chosen Cartier line bundle. -/
theorem effectiveCartierDivisor_vanishing_chosen
    (D : PreWeilRealization geometry H) : ∀ {Y X : V} (i : Y ⟶ X)
      (hi : D.IsEffectiveCartierDivisor i) (a : H X),
    D.pullback i a = 0 →
      a * D.firstChernClass X (D.cartierLineBundle i hi) = 0 := sorry

/-- The concrete pre-Weil theory assembled from the canonical graded de Rham operations
and the explicit comparison models in `PreWeilRealization`. -/
noncomputable def toPreWeilTheory
    (D : PreWeilRealization geometry H) :
    WeilCohomology.SchemePreWeilTheory k k (ULift.{u + 1} k) V dimension product fst snd
      point CH CHgrade
      cyclePullback cyclePushforward pointCycle H
        (fun X ↦ (geometry.scheme.obj X).left.PicardGroup) where
  scheme := geometry.scheme
  scheme_fullyFaithful := geometry.scheme_fullyFaithful
  smooth := geometry.smooth
  projective := geometry.projective
  dimension_eq := geometry.dimension_eq
  schemeProduct := geometry.schemeProduct
  scheme_fst := geometry.scheme_fst
  scheme_snd := geometry.scheme_snd
  schemePoint := geometry.schemePoint
  scheme_essentiallySurjective := D.scheme_essentiallySurjective
  cyclePullback_id := geometry.cyclePullback_id
  cyclePullback_comp := geometry.cyclePullback_comp
  cyclePushforward_id := geometry.cyclePushforward_id
  cyclePushforward_comp := geometry.cyclePushforward_comp
  IsNonemptyEquidimensional := D.IsNonemptyEquidimensional
  nonemptyEquidimensional_iff := D.nonemptyEquidimensional_iff
  product_isNonemptyEquidimensional := D.product_isNonemptyEquidimensional
  tateLine_rank := D.tateLine_rank
  Hgrade := D.Hgrade
  Hgrade_isInternal := D.Hgrade_isInternal
  tateTwist := D.tateTwist
  one_mem := D.one_mem
  mul_mem := D.mul_mem
  gradedComm := D.gradedComm
  pullback := D.pullback
  pullback_mem := D.pullback_mem
  pullback_id := D.pullback_id
  pullback_comp := D.pullback_comp
  coproduct := D.coproduct
  inl := D.inl
  inr := D.inr
  IsEmpty := D.IsGeometricallyEmpty
  axiomA1_empty := D.emptyCohomology
  axiomA1 := D.coproductCohomology
  picardPullback := D.picardPullback
  firstChernClass := D.firstChernClass
  axiomA2 := D.firstChernClass_naturality
  IsProjectiveBundle := D.IsProjectiveBundle
  projectiveBundleLineBundle := D.projectiveBundleLineBundle
  projectiveBundleMap := D.projectiveBundleMap
  projectiveBundleMap_apply := D.projectiveBundleMap_apply
  axiomA3 := D.projectiveBundleMap_bijective
  IsEffectiveCartierDivisor := D.IsEffectiveCartierDivisor
  cartierLineBundle := D.cartierLineBundle
  axiomA4 := D.effectiveCartierDivisor_vanishing_chosen
  pointH0Map := D.pointH0Map
  pointH0Map_apply := D.pointH0Map_apply
  kunnethMap := D.kunnethMap
  kunnethMap_tmul := D.kunnethMap_tmul
  kunnethMap_mem := D.kunnethMap_mem
  axiomA5_point := D.pointH0Map_bijective
  axiomA5 := D.kunnethMap_bijective
  cycleClass := fun X ↦ (D.cycleClass X).toAddMonoidHom
  cycleClass_mem := D.cycleClass_mem
  cycleClass_pullback := D.cycleClass_pullback
  cycleClass_mul := fun X ↦ (D.cycleClass X).map_mul
  diagonalCycle := D.diagonalCycle
  diagonalCycle_product := D.diagonalCycle_product
  integral := D.integral
  integral_vanishes := D.integral_vanishes
  axiomA6 := D.integral_diagonal
  IsBlowupOfSmoothCenter := D.IsBlowupOfSmoothCenter
  axiomA7 := D.blowupPullback_injective

/-- The pre-Weil construction retains the explicitly supplied de Rham grading. -/
theorem toPreWeilTheory_Hgrade (D : PreWeilRealization geometry H) (X : V)
    (i j : ℤ) :
    (D.toPreWeilTheory).Hgrade X (i, j) = D.Hgrade X (i, j) := sorry

/-- The concrete de Rham pre-Weil theory satisfies axiom (A8) in characteristic zero. -/
theorem satisfiesAxiomA8 (D : PreWeilRealization geometry H) :
    D.toPreWeilTheory.SatisfiesAxiomA8 := sorry

/-- The classical Weil-theory candidate produced from the concrete de Rham pre-Weil theory. -/
noncomputable def toClassicalTheory (D : PreWeilRealization geometry H) :
    -- Local instance justification (defeq pin): the output theory uses exactly the grading constructed by the existing pre-Weil conversion owner.
    letI : ∀ X, GradedAlgebra (D.toPreWeilTheory.Hgrade X) := D.toPreWeilTheory.gradedAlgebraHgrade
    WeilCohomology.SchemeClassicalTheory k k (ULift.{u + 1} k) V dimension product fst snd
      point H CH D.toPreWeilTheory.Hgrade CHgrade cyclePullback cyclePushforward :=
  D.toPreWeilTheory.toSchemeClassicalTheory D.satisfiesAxiomA8

/-- The produced classical theory retains the given smooth-projective realization. -/
theorem toClassicalTheory_scheme (D : PreWeilRealization geometry H) :
    -- Local instance justification (defeq pin): project from the same graded-algebra presentation used by toClassicalTheory.
    letI : ∀ X, GradedAlgebra (D.toPreWeilTheory.Hgrade X) := D.toPreWeilTheory.gradedAlgebraHgrade
    D.toClassicalTheory.scheme = geometry.scheme := rfl

/-- Every homogeneous piece of the produced theory is identified with the corresponding
relative de Rham cohomology group. -/
noncomputable def componentEquiv_spec (D : PreWeilRealization geometry H) (X : V) (i j : ℤ) :
    D.toPreWeilTheory.Hgrade X (i, j) ≃ₗ[k]
      cohomologyOverAffineBase (geometry.scheme.obj X).hom i :=
  D.componentEquiv X i j

/-- `componentEquiv_spec` evaluates by the degreewise equivalence stored in the realization. -/
theorem componentEquiv_spec_apply (D : PreWeilRealization geometry H) (X : V) (i j : ℤ)
    (a : D.toPreWeilTheory.Hgrade X (i, j)) :
    D.componentEquiv_spec X i j a = D.componentEquiv X i j a := sorry

end PreWeilRealization

end AlgebraicGeometry.Scheme.DeRham
