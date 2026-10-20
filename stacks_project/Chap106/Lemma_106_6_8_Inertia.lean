module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_18_3
public import stacks_project.Chap94.Lemma_94_16_1_Groupoid
public import stacks_project.Chap106.Definition_106_3_3_FirstOrderThickening
public import stacks_project.Chap106.Lemma_106_6_7
public import stacks_project.Chap106.«106_6_8_1_Comparison»
public import stacks_project.Chap106.«106_6_8_1_Action»
public import stacks_project.Chap106.«106_6_8_1_Sheaf»
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IdentityChart
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift.IdentityChart
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Lift
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Inertia algebraic space and Hom-parameter module of a lift

For a first-order thickening of algebraic stacks, the inertia space of a lift
`ξ` of Remark 106.6.1 is the algebraic space representing `U' ×_{X'} U'`. Its
diagonal and source projection present the infinitesimal automorphism sheaf of
`ξ` as the internal Hom `Hom_{O_U}(Δ^* Ω_{I/U}, C_{U/U'})`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open Limits Bicategory
open Opposite
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

variable {S : Scheme.{u}} {X X' : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack X']
variable (iX : X ⟶ X') [IsThickening iX]
variable {W : AlgebraicSpace S} (x : W.toGroupoids ⟶ X)
variable [Groupoids.Hom.Smooth x]

namespace Object

/-- The structure morphism of a lift is étale. -/
instance instEtale (ξ : Object iX x) : AlgebraicSpace.Etale ξ.a :=
  ξ.etale

namespace ThickeningChart

open FiberedCategoryOver

variable (ξ : Object iX x) [IsFirstOrderThickening iX]
variable (T : Over S) (t : yoneda.obj T ⟶ ξ.U'.functorOfPoints)

/-- The actual discrete Grothendieck map of an arbitrary presheaf map. -/
def presheafMap {P Q : (Over S)ᵒᵖ ⥤ Type u} (f : P ⟶ Q) :
    Groupoids.ofPresheaf P ⟶ Groupoids.ofPresheaf Q :=
  (Sets.toGroupoids (Over S)).map ((Sets.ofPresheaf (Over S)).map f)

/-- The composition comparison comes from the two original functor composition fields. -/
def presheafMapCompIso {P Q R : (Over S)ᵒᵖ ⥤ Type u} (f : P ⟶ Q) (g : Q ⟶ R) :
    presheafMap (f ≫ g) ≅ presheafMap f ≫ presheafMap g :=
  eqToIso <|
    (congrArg (Sets.toGroupoids (Over S)).map
      ((Sets.ofPresheaf (Over S)).map_comp f g)).trans
      ((Sets.toGroupoids (Over S)).map_comp
        ((Sets.ofPresheaf (Over S)).map f) ((Sets.ofPresheaf (Over S)).map g))

/-- The stack map on the specified test scheme. -/
def testMap : GroupoidsOver.slice T ⟶ X' :=
  ((AlgebraicSpace.ofOverSliceEquiv T).inv ≫ presheafMap t) ≫ ξ.x'

/-- The representing space is selected from the original first-order-thickening input. -/
def space : AlgebraicSpace S :=
  (Groupoids.Hom.IsFirstOrderThickening.representable (f := iX)
    (testMap iX x ξ T t)).choose

/-- The original representing morphism to the specified test scheme. -/
def hom : space iX x ξ T t ⟶ AlgebraicSpace.ofOver T :=
  (Groupoids.Hom.IsFirstOrderThickening.representable (f := iX)
    (testMap iX x ξ T t)).choose_spec.choose

/-- This representation certificate is a field of the supplied first-order input. -/
theorem represents : RepresentsBaseChange iX (testMap iX x ξ T t)
    (space iX x ξ T t) (hom iX x ξ T t) :=
  (Groupoids.Hom.IsFirstOrderThickening.representable (f := iX)
    (testMap iX x ξ T t)).choose_spec.choose_spec

/-- Both directions are taken from that same supplied representation certificate. -/
def equiv : TwoFibreProduct.apex.{u + 1, u, u + 1, u} (testMap iX x ξ T t) iX ≌
    (space iX x ξ T t).toGroupoids :=
  (represents iX x ξ T t).choose

/-- The selected representing morphism has the original first-order certificate. -/
theorem firstOrder : AlgebraicSpace.IsFirstOrderThickening (hom iX x ξ T t) :=
  Groupoids.Hom.IsFirstOrderThickening.of_represents (testMap iX x ξ T t)
    (space iX x ξ T t) (hom iX x ξ T t) (represents iX x ξ T t)

/-- The cone on the original lift square, retaining the represented test point. -/
def cone : PseudoPullbackCone iX ξ.x' where
  pt := (space iX x ξ T t).toGroupoids
  fst := (equiv iX x ξ T t).inv ≫ TwoFibreProduct.snd (testMap iX x ξ T t) iX
  snd := ((equiv iX x ξ T t).inv ≫ TwoFibreProduct.fst (testMap iX x ξ T t) iX) ≫
    ((AlgebraicSpace.ofOverSliceEquiv T).inv ≫ presheafMap t)
  iso :=
    (α_ _ _ _) ≪≫
      whiskerLeftIso (equiv iX x ξ T t).inv
        (TwoFibreProduct.comparisonIso (testMap iX x ξ T t) iX).symm ≪≫
      (α_ _ _ _).symm ≪≫ (α_ _ _ _).symm

/-- The map to the reduced lift uses its original, supplied bilimit property. -/
def toLift : space iX x ξ T t ⟶ ξ.U := by
  letI : ξ.cone.IsBilimit := ξ.isPullback
  exact AlgebraicSpace.toGroupoids.eval
    (PseudoPullbackCone.lift (cone iX x ξ T t) ξ.cone)

/-- The scheme representing the original closed immersion on this test. -/
def scheme : Over S :=
  (firstOrder iX x ξ T t).toIsClosedImmersion.presheaf.rep.pullback
    (𝟙 (yoneda.obj T))

/-- The actual closed-immersion projection of the representing scheme. -/
def schemeHom : scheme iX x ξ T t ⟶ T :=
  (firstOrder iX x ξ T t).toIsClosedImmersion.presheaf.rep.snd
    (𝟙 (yoneda.obj T))

/-- The actual other projection of the representing scheme. -/
def schemeFst : yoneda.obj (scheme iX x ξ T t) ⟶ (space iX x ξ T t).functorOfPoints :=
  (firstOrder iX x ξ T t).toIsClosedImmersion.presheaf.rep.fst
    (𝟙 (yoneda.obj T))

variable {P : (Over S)ᵒᵖ ⥤ Type u}
variable (f : P ⟶ ξ.U.functorOfPoints) (g : P ⟶ yoneda.obj T)
variable (w : f ≫ ξ.i = g ≫ t)

/-- A compatible presheaf cone gives an actual cone on the represented stack test. -/
def testCone : PseudoPullbackCone (testMap iX x ξ T t) iX where
  pt := Groupoids.ofPresheaf P
  fst := presheafMap g ≫ (AlgebraicSpace.ofOverSliceEquiv T).hom
  snd := presheafMap f ≫ (AlgebraicSpace.toGroupoids.map ξ.a ≫ x)
  iso :=
    (α_ _ _ _) ≪≫
      whiskerLeftIso (presheafMap g)
        ((α_ _ _ _).symm ≪≫
          whiskerRightIso
            ((α_ _ _ _).symm ≪≫
              whiskerRightIso (AlgebraicSpace.ofOverSliceEquiv T).unit.symm
                (presheafMap t) ≪≫ (λ_ _)) ξ.x') ≪≫
      (α_ _ _ _).symm ≪≫
      whiskerRightIso
        ((presheafMapCompIso g t).symm ≪≫
          eqToIso (congrArg presheafMap w.symm) ≪≫ presheafMapCompIso f ξ.i) ξ.x' ≪≫
      (α_ _ _ _) ≪≫ whiskerLeftIso (presheafMap f) ξ.α.symm ≪≫ (α_ _ _ _).symm

/-- Evaluate the literal two-fibre-product lift through the supplied representing equivalence. -/
def toSpace : P ⟶ (space iX x ξ T t).functorOfPoints where
  app A := TypeCat.ofHom fun a ↦
    Sets.ofPresheaf.fiberToValue (space iX x ξ T t).functorOfPoints A.unop
      ((Groupoids.fiberFunctor
          (TwoFibreProduct.lift (testCone iX x ξ T t f g w) ≫
            (equiv iX x ξ T t).hom) A.unop).obj
        (Sets.ofPresheaf.valueToFiber P A.unop a))
  naturality := sorry

/-- The lift to the original representing scheme uses that supplied pullback certificate. -/
def lift : P ⟶ yoneda.obj (scheme iX x ξ T t) :=
  ((firstOrder iX x ξ T t).toIsClosedImmersion.presheaf.rep.isPullback
    (𝟙 (yoneda.obj T))).lift (toSpace iX x ξ T t f g w) g (by sorry)

/-- The test square retains the actual scheme and both actual projection maps. -/
theorem isPullback :
    IsPullback (schemeFst iX x ξ T t ≫ toLift iX x ξ T t)
      (yoneda.map (schemeHom iX x ξ T t)) ξ.i t :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by sorry)
    (fun c ↦ lift iX x ξ T t c.fst c.snd c.condition)
    (by sorry) (by sorry) (by sorry))

end ThickeningChart

/-- The morphism `i : U ⟶ U'` of a lift along a first-order thickening of
algebraic stacks is a first-order thickening of algebraic spaces. -/
instance instIsFirstOrderThickening (ξ : Object iX x)
    [IsFirstOrderThickening iX] :
    AlgebraicSpace.IsFirstOrderThickening ξ.i where
  toIsClosedImmersion := ⟨⟨fun {T} t ↦
      ⟨ThickeningChart.scheme iX x ξ T t,
        ThickeningChart.schemeHom iX x ξ T t,
        ThickeningChart.schemeFst iX x ξ T t ≫ ThickeningChart.toLift iX x ξ T t,
        ThickeningChart.isPullback iX x ξ T t⟩, by sorry⟩⟩
  square_zero := sorry

/-- The kernel pair is represented by the actual point-pair algebraic space. -/
theorem inertia_isRepresentable (ξ : Object iX x) :
    IsRepresentableByAlgebraicSpace (kernelPair ξ.x') :=
  ⟨kernelPairSpace ξ.U' ξ.x', ⟨kernelPairSpaceEquiv ξ.U' ξ.x'⟩⟩

/-- The inertia algebraic space `I' = U' ×_{x', X', x'} U'` of a lift. -/
def inertia (ξ : Object iX x) : AlgebraicSpace S :=
  kernelPairSpace ξ.U' ξ.x'

/-- The inertia carrier is the specified point-pair algebraic space. -/
theorem inertia_eq (ξ : Object iX x) :
    inertia iX x ξ = kernelPairSpace ξ.U' ξ.x' :=
  rfl

/-- The bicategorical equivalence from the kernel pair of `ξ.x'` to the
groupoid fibration of `inertia ξ`. -/
def inertiaEquiv (ξ : Object iX x) :
    kernelPair ξ.x' ≌ (inertia iX x ξ).toGroupoids :=
  kernelPairSpaceEquiv ξ.U' ξ.x'

/-- The source projection `p' : I' ⟶ U'` of the inertia space. -/
def inertiaSrc (ξ : Object iX x) : inertia iX x ξ ⟶ ξ.U' :=
  kernelPairSpaceSnd ξ.U' ξ.x'

/-- The target projection `q' : I' ⟶ U'` of the inertia space. -/
def inertiaTgt (ξ : Object iX x) : inertia iX x ξ ⟶ ξ.U' :=
  kernelPairSpaceFst ξ.U' ξ.x'

/-- The diagonal morphism `Δ' : U' ⟶ I'` of the inertia space. -/
def inertiaDiagonal (ξ : Object iX x) : ξ.U' ⟶ inertia iX x ξ :=
  kernelPairSpaceDiagonal ξ.U' ξ.x'

/-- The universal inertia 2-cell is the actual point-pair comparison, directed from
the target projection to the source projection. -/
def inertiaUniversalIso (ξ : Object iX x) :
    AlgebraicSpace.toGroupoids.map (inertiaTgt iX x ξ) ≫ ξ.x' ≅
      AlgebraicSpace.toGroupoids.map (inertiaSrc iX x ξ) ≫ ξ.x' :=
  kernelPairSpaceUniversalIso ξ.U' ξ.x'

/-- An identity-chart inertia section has the prescribed reduced diagonal and its source
projection is the identity. Both equations concern the actual point-pair morphisms. -/
def IdentityInertiaSection (ξ : Object iX x) :=
  { δ : ξ.U' ⟶ inertia iX x ξ //
    ξ.i ≫ δ = ξ.i ≫ inertiaDiagonal iX x ξ ∧ δ ≫ inertiaSrc iX x ξ = 𝟙 ξ.U' }

/-- The source projection of inertia is the groupoid source recovered from
`pr1`. -/
theorem inertiaSrc_eq (ξ : Object iX x) :
    inertiaSrc iX x ξ =
      groupoidSource ξ.x' (Bicategory.Equivalence.id _) (inertiaEquiv iX x ξ) :=
  sorry

/-- The target projection of inertia is the groupoid target recovered from
`pr0`. -/
theorem inertiaTgt_eq (ξ : Object iX x) :
    inertiaTgt iX x ξ =
      groupoidTarget ξ.x' (Bicategory.Equivalence.id _) (inertiaEquiv iX x ξ) :=
  sorry

/-- The inertia diagonal is the groupoid identity recovered from the identity
cone on `ξ.x'`. -/
theorem inertiaDiagonal_eq (ξ : Object iX x) :
    inertiaDiagonal iX x ξ =
      groupoidIdentity ξ.x' (Bicategory.Equivalence.id _) (inertiaEquiv iX x ξ) :=
  sorry

/-- On each scheme test, the source is the second stored point. -/
@[simp]
theorem inertiaSrc_app (ξ : Object iX x) (T : (Over S)ᵒᵖ)
    (a : (inertia iX x ξ).functorOfPoints.obj T) :
    (inertiaSrc iX x ξ).app T a = a.snd := rfl

/-- On each scheme test, the target is the first stored point. -/
@[simp]
theorem inertiaTgt_app (ξ : Object iX x) (T : (Over S)ᵒᵖ)
    (a : (inertia iX x ξ).functorOfPoints.obj T) :
    (inertiaTgt iX x ξ).app T a = a.fst := rfl

/-- The diagonal retains the supplied point as its first coordinate. -/
@[simp]
theorem inertiaDiagonal_app_fst (ξ : Object iX x) (T : (Over S)ᵒᵖ)
    (a : ξ.U'.functorOfPoints.obj T) :
    ((inertiaDiagonal iX x ξ).app T a).fst = a := rfl

/-- The diagonal retains the supplied point as its second coordinate. -/
@[simp]
theorem inertiaDiagonal_app_snd (ξ : Object iX x) (T : (Over S)ᵒᵖ)
    (a : ξ.U'.functorOfPoints.obj T) :
    ((inertiaDiagonal iX x ξ).app T a).snd = a := rfl

/-- The diagonal stores the identity comparison of the supplied stack image. -/
@[simp]
theorem inertiaDiagonal_app_iso (ξ : Object iX x) (T : (Over S)ᵒᵖ)
    (a : ξ.U'.functorOfPoints.obj T) :
    ((inertiaDiagonal iX x ξ).app T a).iso = Iso.refl _ := rfl

/-- The source projection splits the inertia diagonal. -/
theorem inertiaDiagonal_comp_src (ξ : Object iX x) :
    inertiaDiagonal iX x ξ ≫ inertiaSrc iX x ξ = 𝟙 ξ.U' :=
  sorry

/-- The target projection splits the inertia diagonal. -/
theorem inertiaDiagonal_comp_tgt (ξ : Object iX x) :
    inertiaDiagonal iX x ξ ≫ inertiaTgt iX x ξ = 𝟙 ξ.U' :=
  sorry

/-- The base change `I = U ×_{U'} I'` of inertia along `ξ.i`. -/
def inertiaSpace (ξ : Object iX x) : AlgebraicSpace S :=
  pullback ξ.i (inertiaSrc iX x ξ)

/-- `inertiaSpace ξ` is the fibre product of `ξ.i` with the inertia source. -/
theorem inertiaSpace_eq (ξ : Object iX x) :
    inertiaSpace iX x ξ = pullback ξ.i (inertiaSrc iX x ξ) :=
  rfl

/-- The projection `p : I ⟶ U` of the base-changed inertia. -/
def inertiaHom (ξ : Object iX x) : inertiaSpace iX x ξ ⟶ ξ.U :=
  pullback.fst ξ.i (inertiaSrc iX x ξ)

/-- The first-order thickening `I ⟶ I'` of the base-changed inertia. -/
def inertiaThickening (ξ : Object iX x) : inertiaSpace iX x ξ ⟶ inertia iX x ξ :=
  pullback.snd ξ.i (inertiaSrc iX x ξ)

/-- The diagonal `Δ : U ⟶ I` of the base-changed inertia. -/
def inertiaRestrict (ξ : Object iX x) : ξ.U ⟶ inertiaSpace iX x ξ :=
  pullback.lift (𝟙 ξ.U) (ξ.i ≫ inertiaDiagonal iX x ξ) sorry

/-- `inertiaHom ξ` is the first projection of the inertia pullback. -/
theorem inertiaHom_eq (ξ : Object iX x) :
    inertiaHom iX x ξ = pullback.fst ξ.i (inertiaSrc iX x ξ) :=
  rfl

/-- `inertiaThickening ξ` is the second projection of the inertia pullback. -/
theorem inertiaThickening_eq (ξ : Object iX x) :
    inertiaThickening iX x ξ = pullback.snd ξ.i (inertiaSrc iX x ξ) :=
  rfl

/-- The base-changed diagonal projects to the identity of `U`. -/
theorem inertiaRestrict_comp_hom (ξ : Object iX x) :
    inertiaRestrict iX x ξ ≫ inertiaHom iX x ξ = 𝟙 ξ.U :=
  sorry

/-- The base-changed diagonal is the restriction of `Δ'` along `ξ.i`. -/
theorem inertiaRestrict_comp_thickening (ξ : Object iX x) :
    inertiaRestrict iX x ξ ≫ inertiaThickening iX x ξ =
      ξ.i ≫ inertiaDiagonal iX x ξ :=
  sorry

/-- The thickening `I ⟶ I'` of base-changed inertia is first-order. -/
instance instInertiaThickeningIsFirstOrder (ξ : Object iX x)
    [IsFirstOrderThickening iX] :
    AlgebraicSpace.IsFirstOrderThickening (inertiaThickening iX x ξ) where
  toIsClosedImmersion := by
    letI : (MorphismProperty.over (X := S)
        (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})).presheaf.IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    let f : ξ.U.functorOfPoints ⟶ ξ.U'.functorOfPoints := ξ.i
    let g : (inertia iX x ξ).functorOfPoints ⟶ ξ.U'.functorOfPoints := inertiaSrc iX x ξ
    let comparison :=
      (AlgebraicSpace.ReasLibPullback.isPullback ξ.i (inertiaSrc iX x ξ)).isoPullback
    have hsquare : IsPullback (C := (Over S)ᵒᵖ ⥤ Type u)
        (inertiaHom iX x ξ : (inertiaSpace iX x ξ).functorOfPoints ⟶ ξ.U.functorOfPoints)
        (inertiaThickening iX x ξ :
          (inertiaSpace iX x ξ).functorOfPoints ⟶ (inertia iX x ξ).functorOfPoints) f g :=
      IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by sorry)
        (fun c ↦ NatTrans.vcomp
          (pullback.lift (f := f) (g := g) c.fst c.snd c.condition) comparison.hom)
        (by sorry) (by sorry) (by sorry))
    exact ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (MorphismProperty.over
        (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})).presheaf)
      hsquare
      (AlgebraicSpace.IsClosedImmersion.presheaf (f := ξ.i))⟩
  square_zero := sorry

/-- The infinitesimal parameter module `Hom_{O_U}(Δ^* Ω_{I/U}, C_{U/U'})` of a
lift. -/
def parameterModule (ξ : Object iX x) [IsFirstOrderThickening iX] :
    RingedSite.ModuleCat.{u + 1} (AlgebraicSpace.commRingedSiteLift ξ.U) :=
  AlgebraicSpace.Hom.Deformation.parameterModule ξ.i (inertiaHom iX x ξ)
    (inertiaRestrict iX x ξ)

/-- `parameterModule ξ` is the ringed-site internal Hom of `Δ^* Ω_{I/U}` with
`C_{U/U'}`. -/
theorem parameterModule_eq (ξ : Object iX x) [IsFirstOrderThickening iX] :
    parameterModule iX x ξ =
      AlgebraicSpace.Hom.Deformation.parameterModule ξ.i (inertiaHom iX x ξ)
        (inertiaRestrict iX x ξ) :=
  rfl

/-- The Hom-parameter module of a first-order lift is quasi-coherent. -/
instance parameterModule_isQuasicoherent (ξ : Object iX x)
    [IsFirstOrderThickening iX] :
    (parameterModule iX x ξ).IsQuasicoherent :=
  sorry

/-- The base-changed inertia square `I = U ×_{U'} I'` is a pullback. -/
theorem inertiaHom_isPullback (ξ : Object iX x) :
    IsPullback (inertiaHom iX x ξ) (inertiaThickening iX x ξ) ξ.i
      (inertiaSrc iX x ξ) :=
  sorry

/-- The inertia diagonal square `U → I → I'`, `U → U' → I'` is a pullback. -/
theorem inertiaRestrict_isPullback (ξ : Object iX x) :
    IsPullback (inertiaRestrict iX x ξ) ξ.i (inertiaThickening iX x ξ)
      (inertiaDiagonal iX x ξ) :=
  sorry

/-- The source carrier and the generic diagonal-section carrier have the same actual map
data, with their reduction equations rewritten by the pullback diagonal. -/
def identityInertiaSectionEquiv (ξ : Object iX x) [IsFirstOrderThickening iX] :
    IdentityInertiaSection iX x ξ ≃
      AlgebraicSpace.Hom.Deformation.IdentitySection ξ.i (inertiaThickening iX x ξ)
        (inertiaSrc iX x ξ) (inertiaRestrict iX x ξ) where
  toFun δ := ⟨δ.val, by sorry, δ.property.2⟩
  invFun δ := ⟨δ.val, by sorry, δ.property.2⟩
  left_inv := sorry
  right_inv := sorry

/-- The actual global parameter/section correspondence for the lift's specified inertia
space. The two functions are common-atlas perturbation and ordered-difference descent. -/
def parameterIdentityInertiaEquiv (ξ : Object iX x) [IsFirstOrderThickening iX] :
    ((AlgebraicSpace.Modules.pullback (inertiaRestrict iX x ξ)).obj
        (AlgebraicSpace.Hom.Deformation.relativeDifferentialsOver (inertiaHom iX x ξ)) ⟶
      AlgebraicSpace.Hom.conormalSheaf ξ.i) ≃ IdentityInertiaSection iX x ξ :=
  AlgebraicSpace.Hom.Deformation.parameterIdentitySectionEquiv ξ.i
      (inertiaThickening iX x ξ) (inertiaSrc iX x ξ) (inertiaHom iX x ξ)
      (inertiaDiagonal iX x ξ) (inertiaRestrict iX x ξ)
      (inertiaRestrict_isPullback iX x ξ) (inertiaHom_isPullback iX x ξ)
      (inertiaDiagonal_comp_src iX x ξ) |>.trans (identityInertiaSectionEquiv iX x ξ).symm

/-- An identity-chart section of the actual parameter module gives a global Hom parameter,
by lowering its lifted components and evaluating the slice at each structural arrow. -/
def identityParameterHomEquiv (ξ : Object iX x) [IsFirstOrderThickening iX]
    (T : Over S) (hU : ξ.U = AlgebraicSpace.ofOver T) :
    ((hU ▸ parameterModule iX x ξ).val.obj
      (op (AlgebraicSpace.SmallEtaleGlueing.idObj T))) ≃
      ((AlgebraicSpace.Modules.pullback (inertiaRestrict iX x ξ)).obj
          (AlgebraicSpace.Hom.Deformation.relativeDifferentialsOver (inertiaHom iX x ξ)) ⟶
        AlgebraicSpace.Hom.conormalSheaf ξ.i) :=
  AlgebraicSpace.Modules.IdentityChart.homEquiv
    ((AlgebraicSpace.Modules.pullback (inertiaRestrict iX x ξ)).obj
      (AlgebraicSpace.Hom.Deformation.relativeDifferentialsOver (inertiaHom iX x ξ)))
    (AlgebraicSpace.Hom.conormalSheaf ξ.i) T hU

/-- Both actual directions of the source identity-chart parameter/inertia correspondence.
This uses the given scheme representation of the reduced lift and adds no comparison input. -/
def identityParameterInertiaEquiv (ξ : Object iX x) [IsFirstOrderThickening iX]
    (T : Over S) (hU : ξ.U = AlgebraicSpace.ofOver T) :
    ((hU ▸ parameterModule iX x ξ).val.obj
      (op (AlgebraicSpace.SmallEtaleGlueing.idObj T))) ≃ IdentityInertiaSection iX x ξ :=
  (identityParameterHomEquiv iX x ξ T hU).trans (parameterIdentityInertiaEquiv iX x ξ)

/-- The forward parameter map is the actual atlas perturbation of the specified diagonal. -/
theorem parameterIdentityInertiaEquiv_apply_val (ξ : Object iX x) [IsFirstOrderThickening iX]
    (θ : (AlgebraicSpace.Modules.pullback (inertiaRestrict iX x ξ)).obj
        (AlgebraicSpace.Hom.Deformation.relativeDifferentialsOver (inertiaHom iX x ξ)) ⟶
      AlgebraicSpace.Hom.conormalSheaf ξ.i) :
    (parameterIdentityInertiaEquiv iX x ξ θ).val =
      AlgebraicSpace.Hom.Deformation.perturbHom ξ.i (inertiaThickening iX x ξ)
        (inertiaRestrict iX x ξ) (inertiaDiagonal iX x ξ)
        (inertiaRestrict_isPullback iX x ξ).toCommSq (inertiaHom iX x ξ) θ := rfl

/-- The reverse map recovers the ordered difference from the same actual section. -/
theorem parameterIdentityInertiaEquiv_symm_apply (ξ : Object iX x) [IsFirstOrderThickening iX]
    (δ : IdentityInertiaSection iX x ξ) :
    (parameterIdentityInertiaEquiv iX x ξ).symm δ =
      AlgebraicSpace.Hom.Deformation.identitySectionParameter ξ.i
        (inertiaThickening iX x ξ) (inertiaSrc iX x ξ) (inertiaHom iX x ξ)
        (inertiaDiagonal iX x ξ) (inertiaRestrict iX x ξ)
        (inertiaRestrict_isPullback iX x ξ) (inertiaHom_isPullback iX x ξ)
        (inertiaDiagonal_comp_src iX x ξ) (identityInertiaSectionEquiv iX x ξ δ) := rfl

/-- Acting by zero retains the specified identity section of inertia. -/
@[simp]
theorem parameterIdentityInertiaEquiv_zero (ξ : Object iX x) [IsFirstOrderThickening iX] :
    (parameterIdentityInertiaEquiv iX x ξ 0).val = inertiaDiagonal iX x ξ := sorry

/-- The source sheaf isomorphism has the constructed perturbation and difference maps. -/
def parameterAutIso (ξ : Object iX x) [IsFirstOrderThickening iX] :
    AlgebraicSpace.Hom.Deformation.parameterSheafEtale ξ.i
        (inertiaHom iX x ξ) (inertiaRestrict iX x ξ) ≅
      AlgebraicSpace.Hom.Deformation.autSheaf ξ.i (inertiaThickening iX x ξ)
        (inertiaSrc iX x ξ) (inertiaDiagonal iX x ξ) (inertiaRestrict iX x ξ)
        (inertiaRestrict_isPullback iX x ξ) :=
  AlgebraicSpace.Hom.Deformation.parameterAutIso ξ.i (inertiaThickening iX x ξ)
    (inertiaSrc iX x ξ) (inertiaHom iX x ξ) (inertiaDiagonal iX x ξ)
    (inertiaRestrict iX x ξ) (inertiaRestrict_isPullback iX x ξ)
    (inertiaHom_isPullback iX x ξ) (inertiaDiagonal_comp_src iX x ξ)

/-- 0CKH for a lift: the Hom-parameter Type sheaf of `ξ` is isomorphic to the
deformation sheaf `autSheaf` of the inertia diagram. -/
theorem parameter_iso_aut (ξ : Object iX x) [IsFirstOrderThickening iX] :
    IsIsomorphic
      (AlgebraicSpace.Hom.Deformation.parameterSheafEtale ξ.i
        (inertiaHom iX x ξ) (inertiaRestrict iX x ξ))
      (AlgebraicSpace.Hom.Deformation.autSheaf ξ.i (inertiaThickening iX x ξ)
        (inertiaSrc iX x ξ) (inertiaDiagonal iX x ξ) (inertiaRestrict iX x ξ)
        (inertiaRestrict_isPullback iX x ξ)) :=
  ⟨parameterAutIso iX x ξ⟩

end Object

end AlgebraicGeometry.AlgebraicStack.Lift
