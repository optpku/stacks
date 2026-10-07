module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.YonedaEvaluation.Chosen
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.YonedaEvaluation.Slice.Chosen
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Equivalence
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.TwoCell
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import stacks_project.Chap101.«101_3_3_1_Isom»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative Isom fibre square of a groupoid-fibred diagonal

The 2-Yoneda lift `a = (x, x', α)` of a `T`-point of `X ×_Y X` and the
canonical diagonal `Δ_f` have 2-fibre product whose sheaf of fibrewise
isomorphism classes over `T` fits in a cartesian square with
`Isom_X(x, x')`, `T`, and `Isom_Y(f(x), f(x'))`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Functor
open FiberedCategoryOver.Groupoids
open Bicategory
open CategoryTheory.Limits
open scoped Bicategory Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

/-- Fibrewise comparison of a composite 1-morphism with the composite of its
fibre functors, at a single object. -/
def fiberFunctorCompObjIso (F : X ⟶ Y) {Z : GroupoidsOver S} (G : Y ⟶ Z)
    {U : Over S} (y : X.p.Fiber U) :
    (fiberFunctor (F ≫ G) U).obj y ≅
      (fiberFunctor G U).obj ((fiberFunctor F U).obj y) :=
  Functor.Fiber.isoMk (Iso.refl _) sorry

/-- Evaluating `representative x ≫ f` at the identity slice recovers `f(x)`. -/
def postcompEvalIso (f : X ⟶ Y) {T : Over S} (x : X.p.Fiber T) :
    (fiberFunctor (YonedaSlice.representative x ≫ f) T).obj
        (BasedCategory.Yoneda.Identity.fiberObj T) ≅
      (fiberFunctor f T).obj x :=
  fiberFunctorCompObjIso (YonedaSlice.representative x) f
      (BasedCategory.Yoneda.Identity.fiberObj T) ≪≫
    (fiberFunctor f T).mapIso (YonedaSlice.representative.fiberObjIso x)

/-- Functoriality of groupoid-fibred Yoneda representatives on fibre isomorphisms. -/
def representativeMapIso {Z : GroupoidsOver S} {U : Over S} {z z' : Z.p.Fiber U}
    (e : z ≅ z') :
    YonedaSlice.representative z ≅ YonedaSlice.representative z' :=
  BasedFunctorIso.lift
    ((ObjectProperty.ι _).mapIso
      ((CartesianBasedFunctor.Yoneda.Chosen.functor Z.p U).mapIso e))

/-- The 2-isomorphism `representative x ≫ f ≅ representative x' ≫ f` induced by `α`. -/
def ofTripleIso (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    YonedaSlice.representative x ≫ f ≅ YonedaSlice.representative x' ≫ f :=
  YonedaSlice.representative.unitIso (YonedaSlice.representative x ≫ f) ≪≫
    representativeMapIso
      (postcompEvalIso f x ≪≫ α ≪≫ (postcompEvalIso f x').symm) ≪≫
    (YonedaSlice.representative.unitIso (YonedaSlice.representative x' ≫ f)).symm

/-- The 2-Yoneda 1-morphism `a : T ⟶ X ×_Y X` associated to the triple `(x, x', α)`. -/
def ofTriple (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    GroupoidsOver.slice T ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f f :=
  PseudoPullbackCone.lift
    { pt := GroupoidsOver.slice T
      fst := YonedaSlice.representative x
      snd := YonedaSlice.representative x'
      iso := ofTripleIso f x x' α }
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f)

/-- First projection of `ofTriple` recovers the Yoneda representative of `x`. -/
def ofTriple_fst (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    ofTriple f x x' α ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f ≅
      YonedaSlice.representative x :=
  PseudoPullbackCone.lift.fstIso
    { pt := GroupoidsOver.slice T
      fst := YonedaSlice.representative x
      snd := YonedaSlice.representative x'
      iso := ofTripleIso f x x' α }
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f)

/-- Second projection of `ofTriple` recovers the Yoneda representative of `x'`. -/
def ofTriple_snd (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    ofTriple f x x' α ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f ≅
      YonedaSlice.representative x' :=
  PseudoPullbackCone.lift.sndIso
    { pt := GroupoidsOver.slice T
      fst := YonedaSlice.representative x
      snd := YonedaSlice.representative x'
      iso := ofTripleIso f x x' α }
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f f)

/-- The 2-fibre product `X ×_{X ×_Y X, a} T`. -/
abbrev apexObj (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} (ofTriple f x x' α)
    (Hom.diagonal.{u + 1, u, u + 1} f)

/-- Projection of the 2-fibre product to the slice category `Over T`. -/
def apexProjection (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    (apexObj f x x' α).total ⥤ Over T :=
  toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u}
    (ofTriple f x x' α) (Hom.diagonal.{u + 1, u, u + 1} f))

/-- The projection `X ×_{X ×_Y X, a} T ⟶ T` is fibred. -/
instance apexProjection_isFibered (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    (apexProjection f x x' α).IsFibered :=
  sorry

/-- Sheaf of fibrewise isomorphism classes of `X ×_{X ×_Y X, a} T` over `T`. -/
def apexSheaf (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    (Over T)ᵒᵖ ⥤ Type (u + 1) :=
  Functor.fiberIsoClassPresheaf (apexProjection f x x' α)

/-- The identity-slice object of `T` over itself, as a section of the lifted Yoneda
presheaf. -/
def basePoint {T : Over S} (T' : Over T) :
    (yoneda.obj (Over.mk (𝟙 T)) ⋙ uliftFunctor.{u + 1, u}).obj (op T') :=
  ULift.up (Over.homMk T'.hom (Category.comp_id T'.hom))

/-- Outer comparison of a 2-fibre-product object in `X ×_Y X`. -/
def toIsomOuterIso (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x')
    (T' : Over T) (q : (apexProjection f x x' α).Fiber T') :
    (toFunctor (ofTriple f x x' α)).obj (BasedCategory.PseudoPullback.fstObj q.1) ≅
      (toFunctor (Hom.diagonal.{u + 1, u, u + 1} f)).obj (BasedCategory.PseudoPullback.sndObj q.1) :=
  BasedCategory.PseudoPullback.comparisonIsoApp q.1

/-- The first projection of `Δ_f` as an isomorphism of total functors. -/
def diagonalFstFunctorIso (f : X ⟶ Y) :
    toFunctor (Hom.diagonal.{u + 1, u, u + 1} f ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f) ≅
      toFunctor (𝟙 X) where
  hom := toNatTrans (fstIso f).hom
  inv := toNatTrans (fstIso f).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The second projection of `Δ_f` as an isomorphism of total functors. -/
def diagonalSndFunctorIso (f : X ⟶ Y) :
    toFunctor (Hom.diagonal.{u + 1, u, u + 1} f ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f) ≅
      toFunctor (𝟙 X) where
  hom := toNatTrans (sndIso f).hom
  inv := toNatTrans (sndIso f).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Total-category comparison `x|_{T'} ≅ x'|_{T'}` obtained by projecting the
outer 2-fibre-product comparison along `Δ_f`. -/
def toIsomTotalIso (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x')
    (T' : Over T) (q : (apexProjection f x x' α).Fiber T') :
    (toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f)).obj
        ((toFunctor (ofTriple f x x' α)).obj
          (BasedCategory.PseudoPullback.fstObj q.1)) ≅
      (toFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f)).obj
        ((toFunctor (ofTriple f x x' α)).obj
          (BasedCategory.PseudoPullback.fstObj q.1)) :=
  (toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f)).mapIso
      (toIsomOuterIso f x x' α T' q) ≪≫
    (diagonalFstFunctorIso f).app (BasedCategory.PseudoPullback.sndObj q.1) ≪≫
      ((diagonalSndFunctorIso f).app
          (BasedCategory.PseudoPullback.sndObj q.1)).symm ≪≫
        (toFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f)).mapIso
          (toIsomOuterIso f x x' α T' q).symm

/-- The first component of a 2-fibre-product fibre object over `T'` is `T'`. -/
theorem toIsomFstObj_eq (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x')
    (T' : Over T) (q : (apexProjection f x x' α).Fiber T') :
    BasedCategory.PseudoPullback.fstObj q.1 = T' :=
  sorry

/-- Total functor of `ofTriple ≫ fst` compared with the Yoneda representative of `x`. -/
def ofTripleFstFunctorIso (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    toFunctor (ofTriple f x x' α ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f) ≅
      toFunctor (YonedaSlice.representative x) where
  hom := toNatTrans (ofTriple_fst f x x' α).hom
  inv := toNatTrans (ofTriple_fst f x x' α).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Total functor of `ofTriple ≫ snd` compared with the Yoneda representative of `x'`. -/
def ofTripleSndFunctorIso (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    toFunctor (ofTriple f x x' α ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f) ≅
      toFunctor (YonedaSlice.representative x') where
  hom := toNatTrans (ofTriple_snd f x x' α).hom
  inv := toNatTrans (ofTriple_snd f x x' α).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The Yoneda representative's total functor is the chosen cartesian section. -/
theorem representative_toFunctor {T : Over S} (z : X.p.Fiber T) :
    ((CartesianBasedFunctor.Yoneda.Chosen.functor X.p T).obj z).toFunctor =
      toFunctor (YonedaSlice.representative z) :=
  sorry

/-- Yoneda-section evaluation of `x` compared with the first projection of `ofTriple`. -/
def toIsomLeftIso (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x')
    (T' : Over T) (q : (apexProjection f x x' α).Fiber T') :
    ((CartesianBasedFunctor.Yoneda.Chosen.functor X.p T).obj x).toFunctor.obj T' ≅
      (toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f)).obj
        ((toFunctor (ofTriple f x x' α)).obj
          (BasedCategory.PseudoPullback.fstObj q.1)) :=
  (eqToIso (representative_toFunctor x)).app T' ≪≫
    (toFunctor (YonedaSlice.representative x)).mapIso
      (eqToIso (toIsomFstObj_eq f x x' α T' q).symm) ≪≫
    (ofTripleFstFunctorIso f x x' α).symm.app
      (BasedCategory.PseudoPullback.fstObj q.1) ≪≫
    (eqToIso (toFunctor.comp (ofTriple f x x' α)
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f))).app
      (BasedCategory.PseudoPullback.fstObj q.1)

/-- Yoneda-section evaluation of `x'` compared with the second projection of `ofTriple`. -/
def toIsomRightIso (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x')
    (T' : Over T) (q : (apexProjection f x x' α).Fiber T') :
    ((CartesianBasedFunctor.Yoneda.Chosen.functor X.p T).obj x').toFunctor.obj T' ≅
      (toFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f)).obj
        ((toFunctor (ofTriple f x x' α)).obj
          (BasedCategory.PseudoPullback.fstObj q.1)) :=
  (eqToIso (representative_toFunctor x')).app T' ≪≫
    (toFunctor (YonedaSlice.representative x')).mapIso
      (eqToIso (toIsomFstObj_eq f x x' α T' q).symm) ≪≫
    (ofTripleSndFunctorIso f x x' α).symm.app
      (BasedCategory.PseudoPullback.fstObj q.1) ≪≫
    (eqToIso (toFunctor.comp (ofTriple f x x' α)
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f))).app
      (BasedCategory.PseudoPullback.fstObj q.1)

/-- Ambient isomorphism `x|_{T'} ≅ x'|_{T'}` between the selected reindexings. -/
def toIsomChosenIso (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x')
    (T' : Over T) (q : (apexProjection f x x' α).Fiber T') :
    ((Functor.Chosen.reindex X.p T'.hom).obj x).1 ≅
      ((Functor.Chosen.reindex X.p T'.hom).obj x').1 :=
  (Functor.Fiber.fiberInclusion : X.p.Fiber T'.left ⥤ X.total).mapIso
      (CartesianBasedFunctor.Yoneda.Slice.Chosen.sectionIso X.p x T').symm ≪≫
    toIsomLeftIso f x x' α T' q ≪≫
      toIsomTotalIso f x x' α T' q ≪≫
        (toIsomRightIso f x x' α T' q).symm ≪≫
          (Functor.Fiber.fiberInclusion : X.p.Fiber T'.left ⥤ X.total).mapIso
            (CartesianBasedFunctor.Yoneda.Slice.Chosen.sectionIso X.p x' T')

/-- Fibre isomorphism between the selected reindexings of `x` and `x'` along `T'`. -/
def toIsomFiberIso (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x')
    (T' : Over T) (q : (apexProjection f x x' α).Fiber T') :
    ((Functor.fiberPseudofunctor X.p).map T'.hom.op.toLoc).toFunctor.obj x ≅
      ((Functor.fiberPseudofunctor X.p).map T'.hom.op.toLoc).toFunctor.obj x' :=
  (Functor.FiberPseudofunctor.mapIso X.p T'.hom).app x ≪≫
    Functor.Fiber.isoMk (toIsomChosenIso f x x' α T' q) sorry ≪≫
      ((Functor.FiberPseudofunctor.mapIso X.p T'.hom).app x').symm

/-- Isomorphism-presheaf section extracted from a 2-fibre-product fibre object. -/
def toIsomSection (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x')
    (T' : Over T) (q : (apexProjection f x x' α).Fiber T') :
    (Functor.isomorphismPresheaf X.p x x').obj (op T') :=
  Pseudofunctor.IsomSubpresheaf.mk (Functor.fiberPseudofunctor X.p) x x'
    (toIsomFiberIso f x x' α T' q).hom

/-- The top arrow of the Isom square, sending a `T'`-point of the 2-fibre product
to the underlying isomorphism `x|_{T'} ⟶ x'|_{T'}`. -/
def toIsom (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    apexSheaf f x x' α ⟶ isom x x' where
  app W :=
    TypeCat.ofHom fun s =>
      ULift.up <|
        Quotient.liftOn s (toIsomSection f x x' α (unop W)) (fun _ _ _ => sorry)
  naturality := sorry

/-- The left vertical arrow of the Isom square, the structure morphism to `T`. -/
def toBase (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    apexSheaf f x x' α ⟶
      yoneda.obj (Over.mk (𝟙 T)) ⋙ uliftFunctor.{u + 1, u} where
  app W := TypeCat.ofHom fun _ => basePoint (unop W)
  naturality := sorry

/-- The square with corners `X ×_{X ×_Y X, a} T`, `Isom_X(x, x')`, `T`, and
`Isom_Y(f(x), f(x'))` is a fibre square of presheaves on `Over T`. -/
theorem isomSquare_isPullback (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    IsPullback (toIsom f x x' α) (toBase f x x' α)
      (isomMap f x x') (alphaSection f x x' α) :=
  sorry

/-- Commutativity of the Isom square. -/
theorem square_comm (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    toIsom f x x' α ≫ isomMap f x x' =
      toBase f x x' α ≫ alphaSection f x x' α :=
  sorry

/-- A `T'`-point of the 2-fibre product exists if and only if there is an
isomorphism `x|_{T'} ⟶ x'|_{T'}` whose image under `isomMap` is `α|_{T'}`. -/
theorem mem_apexSheaf_iff (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') (T' : Over T) :
    Nonempty ((apexSheaf f x x' α).obj (op T')) ↔
      ∃ φ : (isom x x').obj (op T'),
        (isomMap f x x').app (op T') φ =
          (alphaSection f x x' α).app (op T') (basePoint T') :=
  sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal
