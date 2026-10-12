/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.YonedaEvaluation.Chosen
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.YonedaEvaluation.Slice.Chosen
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»
public import stacks_project.Chap95.Lemma_95_18_1_Category

/-!
# Relative map of a finite Hilbert object into a slice 2-fibre product

An object `ξ` of `H_d(X/Y)` determines a 1-morphism
`(Sch/Z)_fppf ⟶ (Sch/U)_fppf ×_{y, Y, F} X` by the universal property of
2-fibre products. After a representing algebraic space `X_y` over `U` is
chosen, the same data recovers a morphism of algebraic spaces over `U`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Functor Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory.TwoFibreProduct

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {X Y : GroupoidsOver S}

/-- Fibrewise comparison of a composite 1-morphism with the composite of its
fibre functors, at a single object. -/
def fiberFunctorCompObjIso {X Y Z : GroupoidsOver S} (F : X ⟶ Y) (G : Y ⟶ Z)
    {U : Over S} (x : X.p.Fiber U) :
    (fiberFunctor (F ≫ G) U).obj x ≅
      (fiberFunctor G U).obj ((fiberFunctor F U).obj x) :=
  Fiber.isoMk (Iso.refl _)
    (IsHomLift.id ((fiberFunctor (F ≫ G) U).obj x).property)

/-- Functoriality of groupoid-fibred Yoneda representatives on fibre isomorphisms. -/
def yonedaMapIso {Z : GroupoidsOver S} {U : Over S} {z z' : Z.p.Fiber U}
    (e : z ≅ z') :
    YonedaSlice.representative z ≅ YonedaSlice.representative z' :=
  BasedFunctorIso.lift
    ((ObjectProperty.ι _).mapIso
      ((CartesianBasedFunctor.Yoneda.Chosen.functor Z.p U).mapIso e))

/-- Evaluating `representative x ≫ F` at the identity slice recovers `F(x)`. -/
def postcompEvalIso (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d) :
    (fiberFunctor (YonedaSlice.representative ξ.x ≫ F) ξ.Z).obj
        (BasedCategory.Yoneda.Identity.fiberObj ξ.Z) ≅
      (fiberFunctor F ξ.Z).obj ξ.x :=
  fiberFunctorCompObjIso (YonedaSlice.representative ξ.x) F
      (BasedCategory.Yoneda.Identity.fiberObj ξ.Z) ≪≫
    (fiberFunctor F ξ.Z).mapIso (YonedaSlice.representative.fiberObjIso ξ.x)

/-- The identity slice of `Z`, postcomposed along `π : Z ⟶ U`, is the slice object
`Over.mk π`. -/
def overMapIdentityIso {U Z : Over S} (π : Z ⟶ U) :
    (fiberFunctor (overMap π) Z).obj (BasedCategory.Yoneda.Identity.fiberObj Z) ≅
      CartesianBasedFunctor.Yoneda.Slice.fiberObj (Over.mk π) :=
  Fiber.isoMk (eqToIso (congrArg Over.mk (Category.id_comp π)))
    (IsHomLift.eqToHom_domain_lift_id (congrArg Over.mk (Category.id_comp π))
      ((fiberFunctor (overMap π) Z).obj
        (BasedCategory.Yoneda.Identity.fiberObj Z)).property)

/-- Chosen reindexing along `π` recovers the cartesian restriction used by `Obj`. -/
def restrictObjReindexIso {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    {p : 𝒳 ⥤ Over S} [p.IsFibered] {U Z : Over S} (ξ : p.Fiber U) (π : Z ⟶ U) :
    Chosen.reindexObj p π ξ ≅ restrictObj ξ π :=
  Fiber.isoMk
    (IsCartesian.domainUniqueUpToIso p π (IsPreFibered.pullbackMap ξ.property π)
      (Chosen.cartesianHom p π ξ))
    (IsCartesian.domainUniqueUpToIso_inv_isHomLift p π
      (IsPreFibered.pullbackMap ξ.property π) (Chosen.cartesianHom p π ξ))

/-- Evaluating the Yoneda representative of `y` at `Over.mk π` recovers `y|_Z`. -/
def representativeRestrictIso {Y : GroupoidsOver S} {U Z : Over S}
    (y : Y.p.Fiber U) (π : Z ⟶ U) :
    (fiberFunctor (YonedaSlice.representative y) Z).obj
        (CartesianBasedFunctor.Yoneda.Slice.fiberObj (Over.mk π)) ≅
      restrictObj y π :=
  CartesianBasedFunctor.Yoneda.Slice.Chosen.evaluationIso Y.p
      (toCartesianBasedFunctor (YonedaSlice.representative y)) (Over.mk π) ≪≫
    (Chosen.reindex Y.p π).mapIso (YonedaSlice.representative.fiberObjIso y) ≪≫
    restrictObjReindexIso y π

/-- Evaluating `overMap π ≫ representative y` at the identity slice recovers `y|_Z`. -/
def restrictEvalIso (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d) :
    (fiberFunctor (overMap ξ.π ≫ YonedaSlice.representative ξ.y) ξ.Z).obj
        (BasedCategory.Yoneda.Identity.fiberObj ξ.Z) ≅
      restrictObj ξ.y ξ.π :=
  fiberFunctorCompObjIso (overMap ξ.π) (YonedaSlice.representative ξ.y)
      (BasedCategory.Yoneda.Identity.fiberObj ξ.Z) ≪≫
    (fiberFunctor (YonedaSlice.representative ξ.y) ξ.Z).mapIso
      (overMapIdentityIso ξ.π) ≪≫
    representativeRestrictIso ξ.y ξ.π

/-- The 2-fibre product `(Sch/U)_fppf ×_{y, Y, F} X` associated to a Hilbert object. -/
abbrev relativeApex (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} (YonedaSlice.representative ξ.y) F

/-- `relativeApex F ξ` is the 2-fibre product of the Yoneda representative of `ξ.y` with `F`. -/
theorem relativeApex_eq (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d) :
    relativeApex F ξ = (YonedaSlice.representative ξ.y) ⊡₂ F := sorry

/-- The 2-cell `overMap π ≫ representative y ≅ representative x ≫ F` induced by `ξ.iso`. -/
def relativeMapIso (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d) :
    overMap ξ.π ≫ YonedaSlice.representative ξ.y ≅
      YonedaSlice.representative ξ.x ≫ F :=
  YonedaSlice.representative.unitIso (overMap ξ.π ≫ YonedaSlice.representative ξ.y) ≪≫
    yonedaMapIso
      (restrictEvalIso F ξ ≪≫ ξ.iso ≪≫ (postcompEvalIso F ξ).symm) ≪≫
    (YonedaSlice.representative.unitIso (YonedaSlice.representative ξ.x ≫ F)).symm

/-- The source-facing 2-commutative square with apex `(Sch/Z)_fppf`. -/
def relativeMapCone (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d) :
    PseudoPullbackCone (YonedaSlice.representative ξ.y) F where
  pt := GroupoidsOver.slice ξ.Z
  fst := overMap ξ.π
  snd := YonedaSlice.representative ξ.x
  iso := relativeMapIso F ξ

/-- The 1-morphism `(x, α) : (Sch/Z)_fppf ⟶ (Sch/U)_fppf ×_{y, Y, F} X`. -/
def relativeMap (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d) :
    GroupoidsOver.slice ξ.Z ⟶ relativeApex F ξ :=
  PseudoPullbackCone.lift (relativeMapCone F ξ)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} (YonedaSlice.representative ξ.y) F)

/-- First projection of `relativeMap` recovers `overMap ξ.π`. -/
def relativeMap_fst (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d) :
    relativeMap F ξ ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} (YonedaSlice.representative ξ.y) F ≅
      overMap ξ.π :=
  PseudoPullbackCone.lift.fstIso (relativeMapCone F ξ)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} (YonedaSlice.representative ξ.y) F)

/-- Second projection of `relativeMap` recovers the Yoneda representative of `ξ.x`. -/
def relativeMap_snd (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d) :
    relativeMap F ξ ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} (YonedaSlice.representative ξ.y) F ≅
      YonedaSlice.representative ξ.x :=
  PseudoPullbackCone.lift.sndIso (relativeMapCone F ξ)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} (YonedaSlice.representative ξ.y) F)

/-- `relativeMap` is the universal lift of `relativeMapCone`. -/
theorem relativeMap_eq (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d) :
    relativeMap F ξ =
      PseudoPullbackCone.lift (relativeMapCone F ξ)
        (TwoFibreProduct.cone.{u + 1, u, u + 1, u} (YonedaSlice.representative ξ.y) F) :=
  sorry

/-- The morphism `x_α : Z ⟶ X_y` of algebraic spaces over `U` recovered from `(x, α)`
and a presentation of the slice 2-fibre product. The structure morphism `fy`
is not an input to this recovery; it appears in `relativeSpaceHom_comp`. -/
def relativeSpaceHom (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d)
    (Xy : AlgebraicSpace S) (e : relativeApex F ξ ≌ Xy.toGroupoids) :
    ofOver ξ.Z ⟶ Xy :=
  toGroupoids.recover (ofOverSliceEquiv ξ.Z).symm e (relativeMap F ξ)

/-- If the presentation identifies the first projection with `fy`, then `relativeSpaceHom`
lies over `U`. -/
theorem relativeSpaceHom_comp (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d)
    (Xy : AlgebraicSpace S) (fy : Xy ⟶ ofOver ξ.U)
    (e : relativeApex F ξ ≌ Xy.toGroupoids)
    (h_fst : Nonempty
      (e.hom ≫ toGroupoids.map fy ≫ (ofOverSliceEquiv ξ.U).hom ≅
        TwoFibreProduct.fst.{u + 1, u, u + 1, u}
          (YonedaSlice.representative ξ.y) F)) :
    relativeSpaceHom F ξ Xy e ≫ fy = ofOverMap ξ.π := sorry

/-- `relativeMap` induces `relativeSpaceHom` relative to the chosen presentations. -/
theorem relativeSpaceHom_induces (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d)
    (Xy : AlgebraicSpace S) (e : relativeApex F ξ ≌ Xy.toGroupoids) :
    toGroupoids.InducesHom (relativeMap F ξ) (ofOverSliceEquiv ξ.Z).symm e
      (relativeSpaceHom F ξ Xy e) := sorry

/-- A representing algebraic space for the slice 2-fibre product supplies the projection
triangle used by `relativeSpaceHom_comp`. -/
theorem relativeSpaceHom_of_representsBaseChange (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d)
    (Xy : AlgebraicSpace S) (fy : Xy ⟶ ofOver ξ.U)
    (h : RepresentsBaseChange F (YonedaSlice.representative ξ.y) Xy fy) :
    ∃ e : relativeApex F ξ ≌ Xy.toGroupoids,
      Nonempty
        (e.hom ≫ toGroupoids.map fy ≫ (ofOverSliceEquiv ξ.U).hom ≅
          TwoFibreProduct.fst.{u + 1, u, u + 1, u}
            (YonedaSlice.representative ξ.y) F) := sorry


end AlgebraicGeometry.FiniteHilbertStack
