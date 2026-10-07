module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import stacks_project.Chap98.Definition_98_22_1_DeformationSituation
public import stacks_project.Chap98.Lemma_98_21_1

/-!
# Objects over spectra through an affine open of the base

An object of a category fibred in groupoids over `(Sch/S)_fppf` lying over
`Spec(A) → S`, together with an explicit factorization through an affine open
`Spec(Λ) ⊂ S`. This is the standing context for naive obstruction theories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

/-- An object of `X` over `Spec(A) ⟶ S` together with an explicit factorization
through an affine open `Spec(Λ) ⊂ S`. -/
structure ObjectOverAffineOpen (X : GroupoidsOver S) extends ObjectOverSpec X where
  /-- Underlying commutative ring `Λ` of the affine open. -/
  base : Type u
  [baseCommRing : CommRing base]
  /-- Open immersion `Spec(Λ) ⟶ S`. -/
  openImmersion : Spec (CommRingCat.of base) ⟶ S
  [isOpenImmersion : IsOpenImmersion openImmersion]
  [algebra : Algebra base carrier]
  /-- The structure map factors as `Spec(A) ⟶ Spec(Λ) ⟶ S`. -/
  factor :
    Spec.map (CommRingCat.ofHom (algebraMap base carrier)) ≫ openImmersion = toS

attribute [instance] ObjectOverAffineOpen.baseCommRing
attribute [instance] ObjectOverAffineOpen.isOpenImmersion
attribute [instance] ObjectOverAffineOpen.algebra

namespace ObjectOverAffineOpen

variable {X : GroupoidsOver S}

/-- Package an object over `Spec(A)` with an explicit affine open `Spec(Λ)` and
a factorization of `Spec(A) ⟶ S`. -/
def of (ξ : ObjectOverSpec X) (base : Type u) [CommRing base]
    (openImmersion : Spec (CommRingCat.of base) ⟶ S) [IsOpenImmersion openImmersion]
    [Algebra base ξ.carrier]
    (factor :
      Spec.map (CommRingCat.ofHom (algebraMap base ξ.carrier)) ≫ openImmersion = ξ.toS) :
    ObjectOverAffineOpen X where
  toObjectOverSpec := ξ
  base := base
  openImmersion := openImmersion
  factor := factor

/-- An `ObjectOverAffineOpen` is an object over `Spec(A) ⟶ S` factoring through
an open immersion `Spec(Λ) ⟶ S`. -/
theorem spec (ξ : ObjectOverAffineOpen X) :
    IsOpenImmersion ξ.openImmersion ∧
      (Spec.map (CommRingCat.ofHom (algebraMap ξ.base ξ.carrier)) ≫
          ξ.openImmersion = ξ.toS) ∧
        ξ.toS.MapsIntoAffineOpen ∧ X.p.obj ξ.obj = Over.mk ξ.toS :=
  sorry

/-- The algebra map `Λ ⟶ A` as a morphism of bundled commutative rings. -/
def algebraHom (ξ : ObjectOverAffineOpen X) :
    CommRingCat.of ξ.base ⟶ CommRingCat.of ξ.carrier :=
  CommRingCat.ofHom (algebraMap ξ.base ξ.carrier)

/-- `algebraHom` is `ofHom` of the structure map `Λ ⟶ A`. -/
theorem algebraHom_eq (ξ : ObjectOverAffineOpen X) :
    ξ.algebraHom = CommRingCat.ofHom (algebraMap ξ.base ξ.carrier) :=
  sorry

/-- A morphism of objects over spectra along `A → B` over a shared affine open
`Spec(Λ)`, with restriction arrow `y ⟶ x`. -/
structure Hom (ξ η : ObjectOverAffineOpen X)
    extends ObjectOverSpec.Hom ξ.toObjectOverSpec η.toObjectOverSpec where
  /-- The two objects use the same affine open `Spec(Λ)`. -/
  baseEq : η.base = ξ.base
  /-- The `Λ`-algebra structure on `B` through `A → B`. -/
  algebra : Algebra ξ.base η.carrier
  /-- `Spec(B) ⟶ Spec(Λ) ⟶ S` recovers the structure map of `B`. -/
  sourceFactor :
    Spec.map (CommRingCat.ofHom (@algebraMap ξ.base η.carrier _ _ algebra)) ≫
      ξ.openImmersion = η.toS

/-- Package a morphism of objects over spectra, the shared affine open, and the
induced `Λ`-algebra structure on `B`. -/
def Hom.of {ξ η : ObjectOverAffineOpen X}
    (toHom : ObjectOverSpec.Hom ξ.toObjectOverSpec η.toObjectOverSpec)
    (baseEq : η.base = ξ.base)
    (algebra : Algebra ξ.base η.carrier)
    (sourceFactor :
      Spec.map (CommRingCat.ofHom (@algebraMap ξ.base η.carrier _ _ algebra)) ≫
        ξ.openImmersion = η.toS) :
    Hom ξ η where
  toHom := toHom
  baseEq := baseEq
  algebra := algebra
  sourceFactor := sourceFactor

/-- A morphism of objects through a shared affine open is a ring map `A → B`
over `Λ` together with a restriction arrow `y ⟶ x`. -/
theorem Hom.spec {ξ η : ObjectOverAffineOpen X} (f : Hom ξ η) :
    η.base = ξ.base ∧
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ ξ.toS = η.toS ∧
        X.p.IsHomLift (ObjectOverSpec.specOverMap f.toRingHom f.toS_comp) f.restriction ∧
          (Spec.map (CommRingCat.ofHom
              (@algebraMap ξ.base η.carrier _ _ f.algebra)) ≫
            ξ.openImmersion = η.toS) :=
  sorry

/-- The algebra map `Λ ⟶ B` induced by a morphism over a shared affine open. -/
def Hom.algebraHom {ξ η : ObjectOverAffineOpen X} (f : Hom ξ η) :
    CommRingCat.of ξ.base ⟶ CommRingCat.of η.carrier :=
  CommRingCat.ofHom (@algebraMap ξ.base η.carrier _ _ f.algebra)

/-- `Hom.algebraHom` is `ofHom` of the structure map `Λ ⟶ B`. -/
theorem Hom.algebraHom_eq {ξ η : ObjectOverAffineOpen X} (f : Hom ξ η) :
    f.algebraHom = CommRingCat.ofHom (@algebraMap ξ.base η.carrier _ _ f.algebra) :=
  sorry

/-- The `Λ`-algebra map `A →ₐ[Λ] B` underlying a morphism over a shared affine
open. -/
def Hom.algHom {ξ η : ObjectOverAffineOpen X} (f : Hom ξ η) :
    @AlgHom ξ.base ξ.carrier η.carrier _ _ _ ξ.algebra f.algebra :=
  -- Local instance justification (proof-local temporary data): activate the
  -- Λ-algebra on B stored on this morphism so the AlgHom package elaborates.
  letI := f.algebra
  { toRingHom := f.toRingHom
    commutes' := sorry }

/-- `Hom.algHom` has underlying ring homomorphism `toRingHom`. -/
theorem Hom.algHom_toRingHom {ξ η : ObjectOverAffineOpen X} (f : Hom ξ η) :
    @AlgHom.toRingHom ξ.base ξ.carrier η.carrier _ _ _ ξ.algebra f.algebra f.algHom =
      f.toRingHom :=
  sorry

/-- Identity morphism of an object through an affine open. -/
def Hom.id (ξ : ObjectOverAffineOpen X) : Hom ξ ξ where
  toHom := ObjectOverSpec.Hom.id ξ.toObjectOverSpec
  baseEq := rfl
  algebra := ξ.algebra
  sourceFactor := ξ.factor

/-- Composition of morphisms of objects through a shared affine open. -/
def Hom.comp {ξ η ζ : ObjectOverAffineOpen X} (f : Hom ξ η) (g : Hom η ζ) :
    Hom ξ ζ where
  toHom := ObjectOverSpec.Hom.comp f.toHom g.toHom
  baseEq := g.baseEq.trans f.baseEq
  algebra :=
    RingHom.toAlgebra
      (g.toRingHom.comp (@algebraMap ξ.base η.carrier _ _ f.algebra))
  sourceFactor := sorry

end ObjectOverAffineOpen

namespace ObjectOverSpec

variable {X : GroupoidsOver S}

/-- The fibre object of `x` over `Spec(A) ⟶ S`. -/
def toFiber (ξ : ObjectOverSpec X) : X.p.Fiber (Over.mk ξ.toS) :=
  Functor.Fiber.mk ξ.over_obj

/-- `toFiber ξ` is the fibre point associated to `ξ.over_obj`. -/
theorem toFiber_eq_mk (ξ : ObjectOverSpec X) :
    ξ.toFiber = Functor.Fiber.mk ξ.over_obj :=
  sorry

end ObjectOverSpec

namespace ObjectOverAffineOpen

variable {X : GroupoidsOver S}

/-- The restriction arrow of `f` lies over `𝟙 ≫ Spec(A → B)` in `Over S`. -/
theorem Hom.restriction_id_comp_isHomLift {ξ η : ObjectOverAffineOpen X}
    (f : Hom ξ η) :
    X.p.IsHomLift
      (𝟙 (Over.mk η.toS) ≫
        specOverHom (CommRingCat.ofHom f.toRingHom) f.toS_comp)
      f.restriction :=
  sorry

/-- The cartesian factor of `f.restriction` through `Chosen.cartesianHom` is
vertical. -/
theorem Hom.cartesianFactor_isHomLift {ξ η : ObjectOverAffineOpen X}
    (f : Hom ξ η) :
    X.p.IsHomLift (𝟙 (Over.mk η.toS))
      (FiberedCategoryOver.Groupoids.cartesianFactorOf X.p
        (specOverHom (CommRingCat.ofHom f.toRingHom) f.toS_comp)
        (𝟙 (Over.mk η.toS)) ξ.toObjectOverSpec.toFiber f.restriction
        (Hom.restriction_id_comp_isHomLift f)) :=
  sorry

/-- The unique fibre arrow `x|_Spec(B) ⟶ y` obtained by cartesian factorization
of the restriction `y ⟶ x` through `Chosen.cartesianHom`. -/
def Hom.fiberArrow {ξ η : ObjectOverAffineOpen X} (f : Hom ξ η) :
    Chosen.reindexObj X.p
      (specOverHom (CommRingCat.ofHom f.toRingHom) f.toS_comp)
      ξ.toObjectOverSpec.toFiber ⟶ η.toObjectOverSpec.toFiber :=
  CategoryTheory.inv
    (⟨FiberedCategoryOver.Groupoids.cartesianFactorOf X.p
        (specOverHom (CommRingCat.ofHom f.toRingHom) f.toS_comp)
        (𝟙 (Over.mk η.toS)) ξ.toObjectOverSpec.toFiber f.restriction
        (Hom.restriction_id_comp_isHomLift f),
      Hom.cartesianFactor_isHomLift f⟩ :
      η.toObjectOverSpec.toFiber ⟶
        Chosen.reindexObj X.p
          (specOverHom (CommRingCat.ofHom f.toRingHom) f.toS_comp)
          ξ.toObjectOverSpec.toFiber)

/-- `fiberArrow` is the inverse of the cartesian factor of `f.restriction`
through `Chosen.cartesianHom`. -/
theorem Hom.fiberArrow_eq {ξ η : ObjectOverAffineOpen X} (f : Hom ξ η) :
    f.fiberArrow =
      CategoryTheory.inv
        (⟨FiberedCategoryOver.Groupoids.cartesianFactorOf X.p
            (specOverHom (CommRingCat.ofHom f.toRingHom) f.toS_comp)
            (𝟙 (Over.mk η.toS)) ξ.toObjectOverSpec.toFiber f.restriction
            (Hom.restriction_id_comp_isHomLift f),
          Hom.cartesianFactor_isHomLift f⟩ :
          η.toObjectOverSpec.toFiber ⟶
            Chosen.reindexObj X.p
              (specOverHom (CommRingCat.ofHom f.toRingHom) f.toS_comp)
              ξ.toObjectOverSpec.toFiber) :=
  sorry

/-- The cartesian factor of `f.restriction` through `Chosen.cartesianHom`
recovers the restriction arrow. -/
theorem Hom.fiberArrow_fac {ξ η : ObjectOverAffineOpen X} (f : Hom ξ η) :
    Fiber.fiberInclusion.map (CategoryTheory.inv f.fiberArrow) ≫
      Chosen.cartesianHom X.p
        (specOverHom (CommRingCat.ofHom f.toRingHom) f.toS_comp)
        ξ.toObjectOverSpec.toFiber =
      f.restriction :=
  sorry

end ObjectOverAffineOpen

namespace DeformationSituation

variable {X : GroupoidsOver S}

/-- A square-zero thickening of an object through an affine open `Spec(Λ)`,
recorded as a deformation situation of that object with `A'` a `Λ`-algebra. -/
structure OverAffine (ξ : ObjectOverAffineOpen X) where
  /-- The underlying deformation situation `(x, A' → A)`. -/
  situation : DeformationSituation X
  /-- The deformation situation has the same object over `Spec(A)` as `ξ`. -/
  isOver : situation.toObjectOverSpec = ξ.toObjectOverSpec
  /-- The `Λ`-algebra structure on `A'`. -/
  algebra : Algebra ξ.base situation.source
  /-- `Spec(A') ⟶ Spec(Λ) ⟶ S` recovers the structure map of `A'`. -/
  sourceFactor :
    Spec.map (CommRingCat.ofHom
        (@algebraMap ξ.base situation.source _ _ algebra)) ≫
      ξ.openImmersion = situation.sourceToS

/-- Package a deformation situation of `ξ` whose source is a `Λ`-algebra
factoring through the same affine open. -/
def OverAffine.of (ξ : ObjectOverAffineOpen X)
    (situation : DeformationSituation X)
    (isOver : situation.toObjectOverSpec = ξ.toObjectOverSpec)
    (algebra : Algebra ξ.base situation.source)
    (sourceFactor :
      Spec.map (CommRingCat.ofHom
          (@algebraMap ξ.base situation.source _ _ algebra)) ≫
        ξ.openImmersion = situation.sourceToS) :
    OverAffine ξ where
  situation := situation
  isOver := isOver
  algebra := algebra
  sourceFactor := sourceFactor

/-- An `OverAffine` thickening is a square-zero extension `A' → A` of
`Λ`-algebras with the same object `x` over `Spec(A)`. -/
theorem OverAffine.spec {ξ : ObjectOverAffineOpen X} (τ : OverAffine ξ) :
    τ.situation.toObjectOverSpec = ξ.toObjectOverSpec ∧
      τ.situation.toCarrier.IsSquareZeroExtension ∧
        (Spec.map (CommRingCat.ofHom
            (@algebraMap ξ.base τ.situation.source _ _ τ.algebra)) ≫
          ξ.openImmersion = τ.situation.sourceToS) :=
  sorry

/-- The square-zero map `A' → A` transported to the carrier of `ξ`. -/
def OverAffine.toCarrierOver {ξ : ObjectOverAffineOpen X} (τ : OverAffine ξ) :
    τ.situation.source →+* ξ.carrier where
  toFun x :=
    cast (congrArg ObjectOverSpec.carrier τ.isOver) (τ.situation.toCarrier x)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- `toCarrierOver` agrees with `toCarrier` after identifying carriers. -/
theorem OverAffine.toCarrierOver_eq {ξ : ObjectOverAffineOpen X}
    (τ : OverAffine ξ) (x : τ.situation.source) :
    τ.toCarrierOver x =
      cast (congrArg ObjectOverSpec.carrier τ.isOver) (τ.situation.toCarrier x) :=
  sorry

/-- The `Λ`-algebra map `A' →ₐ[Λ] A` of an affine-open deformation situation,
targeted at the carrier of `ξ`. -/
def OverAffine.algHom {ξ : ObjectOverAffineOpen X} (τ : OverAffine ξ) :
    @AlgHom ξ.base τ.situation.source ξ.carrier _ _ _ τ.algebra ξ.algebra :=
  -- Local instance justification (proof-local temporary data): activate the
  -- stored Λ-algebra structure on A' for this thickening.
  letI := τ.algebra
  { toRingHom := τ.toCarrierOver
    commutes' := sorry }

/-- `OverAffine.algHom` has underlying ring homomorphism `toCarrierOver`. -/
theorem OverAffine.algHom_toRingHom {ξ : ObjectOverAffineOpen X} (τ : OverAffine ξ) :
    @AlgHom.toRingHom ξ.base τ.situation.source ξ.carrier _ _ _
      τ.algebra ξ.algebra τ.algHom =
      τ.toCarrierOver :=
  sorry

end DeformationSituation

end AlgebraicGeometry.GroupoidsOver
