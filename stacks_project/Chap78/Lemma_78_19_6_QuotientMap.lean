module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import stacks_project.Chap78.Definition_78_19_1_QuotientSheaf

/-!
# Restriction-induced maps of fppf quotient sheaves

This module records the restriction of a pre-relation along a morphism over the
base and the induced maps of quotient presheaves and fppf quotient sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Limits ConcreteCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- The restriction of a pre-relation `P` along `g : U' ⟶ U`, realized as the
pullback of `P` along `prod.map g g`. -/
abbrev restrict {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) : PreRelation U' :=
  (Over.pullback (prod.map g g)).obj P

/-- The defining map of a restricted pre-relation is the second pullback projection. -/
theorem restrict_hom {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) :
    (P.restrict g).hom = pullback.snd P.hom (prod.map g g) :=
  sorry

/-- The first pullback projection intertwines the target maps of a restriction. -/
theorem restrict_t_comp {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) :
    pullback.fst P.hom (prod.map g g) ≫ P.t = (P.restrict g).t ≫ g :=
  ((congrArg (fun k ↦ pullback.fst P.hom (prod.map g g) ≫ k)
      (rfl : P.t = P.hom ≫ prod.fst)).trans
    (pullback.condition_assoc (prod.fst : U ⨯ U ⟶ U))).trans
    (((congrArg (fun k ↦ pullback.snd P.hom (prod.map g g) ≫ k) (prod.map_fst g g)).trans
        (Category.assoc (pullback.snd P.hom (prod.map g g)) prod.fst g).symm).trans
      (congrArg (fun k ↦ k ≫ g)
        (rfl : pullback.snd P.hom (prod.map g g) ≫ prod.fst = (P.restrict g).t)))

/-- The first pullback projection intertwines the source maps of a restriction. -/
theorem restrict_s_comp {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) :
    pullback.fst P.hom (prod.map g g) ≫ P.s = (P.restrict g).s ≫ g :=
  ((congrArg (fun k ↦ pullback.fst P.hom (prod.map g g) ≫ k)
      (rfl : P.s = P.hom ≫ prod.snd)).trans
    (pullback.condition_assoc (prod.snd : U ⨯ U ⟶ U))).trans
    (((congrArg (fun k ↦ pullback.snd P.hom (prod.map g g) ≫ k) (prod.map_snd g g)).trans
        (Category.assoc (pullback.snd P.hom (prod.map g g)) prod.snd g).symm).trans
      (congrArg (fun k ↦ k ≫ g)
        (rfl : pullback.snd P.hom (prod.map g g) ≫ prod.snd = (P.restrict g).s)))

/-- The first pullback projection intertwines the target maps on underlying algebraic spaces. -/
theorem restrict_t_comp_left {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) :
    (pullback.fst P.hom (prod.map g g)).left ≫ P.t.left =
      (P.restrict g).t.left ≫ g.left :=
  ((Over.comp_left _ _ _ (pullback.fst P.hom (prod.map g g)) P.t).symm.trans
    (congrArg Over.Hom.left (P.restrict_t_comp g))).trans
    (Over.comp_left _ _ _ (P.restrict g).t g)

/-- The first pullback projection intertwines the source maps on underlying algebraic spaces. -/
theorem restrict_s_comp_left {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) :
    (pullback.fst P.hom (prod.map g g)).left ≫ P.s.left =
      (P.restrict g).s.left ≫ g.left :=
  ((Over.comp_left _ _ _ (pullback.fst P.hom (prod.map g g)) P.s).symm.trans
    (congrArg Over.Hom.left (P.restrict_s_comp g))).trans
    (Over.comp_left _ _ _ (P.restrict g).s g)

/-- The first pullback projection intertwines target maps on scheme-valued points. -/
theorem restrict_t_comp_app {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) (T : Over S) :
    (pullback.fst P.hom (prod.map g g)).left.app (op T) ≫ P.t.left.app (op T) =
      (P.restrict g).t.left.app (op T) ≫ g.left.app (op T) :=
  ((NatTrans.comp_app (pullback.fst P.hom (prod.map g g)).left P.t.left (op T)).symm.trans
    (NatTrans.congr_app (P.restrict_t_comp_left g) (op T))).trans
    (NatTrans.comp_app (P.restrict g).t.left g.left (op T))

/-- The first pullback projection intertwines source maps on scheme-valued points. -/
theorem restrict_s_comp_app {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) (T : Over S) :
    (pullback.fst P.hom (prod.map g g)).left.app (op T) ≫ P.s.left.app (op T) =
      (P.restrict g).s.left.app (op T) ≫ g.left.app (op T) :=
  ((NatTrans.comp_app (pullback.fst P.hom (prod.map g g)).left P.s.left (op T)).symm.trans
    (NatTrans.congr_app (P.restrict_s_comp_left g) (op T))).trans
    (NatTrans.comp_app (P.restrict g).s.left g.left (op T))

/-- Applying `g` to the target projection of a restricted relation recovers the original
target projection of the first pullback projection. -/
theorem restrict_t_app {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) {T : Over S}
    (r : (P.restrict g).left.left.functorOfPoints.obj (op T)) :
    P.t.left.app (op T) ((pullback.fst P.hom (prod.map g g)).left.app (op T) r) =
      g.left.app (op T) ((P.restrict g).t.left.app (op T) r) :=
  (Eq.symm
      (CategoryTheory.comp_apply
        ((pullback.fst P.hom (prod.map g g)).left.app (op T))
        (P.t.left.app (op T)) r)).trans
    ((ConcreteCategory.congr_hom (P.restrict_t_comp_app g T) r).trans
      (CategoryTheory.comp_apply
        ((P.restrict g).t.left.app (op T)) (g.left.app (op T)) r))

/-- Applying `g` to the source projection of a restricted relation recovers the original
source projection of the first pullback projection. -/
theorem restrict_s_app {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) {T : Over S}
    (r : (P.restrict g).left.left.functorOfPoints.obj (op T)) :
    P.s.left.app (op T) ((pullback.fst P.hom (prod.map g g)).left.app (op T) r) =
      g.left.app (op T) ((P.restrict g).s.left.app (op T) r) :=
  (Eq.symm
      (CategoryTheory.comp_apply
        ((pullback.fst P.hom (prod.map g g)).left.app (op T))
        (P.s.left.app (op T)) r)).trans
    ((ConcreteCategory.congr_hom (P.restrict_s_comp_app g T) r).trans
      (CategoryTheory.comp_apply
        ((P.restrict g).s.left.app (op T)) (g.left.app (op T)) r))

/-- Related scheme-valued points of a restriction remain related after applying `g`. -/
theorem restrict_schemePointRel {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) {T : Over S}
    {x y : U'.left.functorOfPoints.obj (op T)}
    (h : (P.restrict g).schemePointRel T x y) :
    P.schemePointRel T (g.left.app (op T) x) (g.left.app (op T) y) :=
  match h with
  | ⟨r, hx, hy⟩ =>
    ⟨(pullback.fst P.hom (prod.map g g)).left.app (op T) r,
      (P.restrict_t_app g r).trans (congrArg (g.left.app (op T)) hx),
      (P.restrict_s_app g r).trans (congrArg (g.left.app (op T)) hy)⟩

/-- The map of quotient presheaves induced by restriction of a pre-relation along `g`. -/
def quotientPresheafMap {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) :
    (P.restrict g).quotientPresheaf ⟶ P.quotientPresheaf where
  app T :=
    TypeCat.ofHom <|
      Quot.map (g.left.app T) fun _ _ h ↦ P.restrict_schemePointRel g h
  naturality := sorry

/-- The restriction-induced quotient presheaf map sends the class of a point to the
class of its image under `g`. -/
theorem quotientPresheafMap_mk {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) (T : Over S)
    (a : U'.left.functorOfPoints.obj (op T)) :
    (P.quotientPresheafMap g).app (op T) (Quot.mk ((P.restrict g).schemePointRel T) a) =
      Quot.mk (P.schemePointRel T) (g.left.app (op T) a) :=
  sorry

/-- The map of fppf quotient sheaves `U'/R' ⟶ U/R` induced by restriction along `g`. -/
def quotientSheafMap {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) :
    (P.restrict g).quotientSheaf ⟶ P.quotientSheaf :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
    (Functor.whiskerRight (P.quotientPresheafMap g) uliftFunctor.{u + 1, u})

/-- The restriction-induced quotient sheaf map sends the class of a point of `U'` to
the class of its image under `g`. -/
theorem quotientSheafMap_quotientClass {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U U' : Over B} (P : PreRelation U) (g : U' ⟶ U) (T : Over S)
    (a : U'.left.functorOfPoints.obj (op T)) :
    (P.quotientSheafMap g).hom.app (op T) ((P.restrict g).quotientClass T a) =
      P.quotientClass T (g.left.app (op T) a) :=
  sorry

/-- The quotient projections form a commutative square with the restriction-induced
quotient sheaf map. -/
theorem quotientMap_comp_quotientSheafMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U U' : Over B} (P : PreRelation U) (g : U' ⟶ U) :
    (P.restrict g).quotientMap ≫ P.quotientSheafMap g =
      uliftSheafMap g.left ≫ P.quotientMap :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
