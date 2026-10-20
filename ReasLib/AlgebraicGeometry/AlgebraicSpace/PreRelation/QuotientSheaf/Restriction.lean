/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf.LocallySurjective

/-!
# Restriction-induced maps of quotient sheaves

Pullback of a pre-relation induces canonical maps on quotient presheaves and fppf
quotient sheaves. For pre-equivalence relations these maps are injective, and they
are isomorphisms when the restricting morphism is surjective as a map of sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Limits ConcreteCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- The first pullback projection intertwines the target maps of a restriction. -/
private theorem restrict_t_comp {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) :
    Limits.pullback.fst P.hom (prod.map g g) ≫ P.t = (P.pullback g).t ≫ g :=
  ((congrArg (fun k ↦ Limits.pullback.fst P.hom (prod.map g g) ≫ k)
      (rfl : P.t = P.hom ≫ prod.fst)).trans
    (Limits.pullback.condition_assoc (prod.fst : U ⨯ U ⟶ U))).trans
    (((congrArg (fun k ↦ Limits.pullback.snd P.hom (prod.map g g) ≫ k) (prod.map_fst g g)).trans
        (Category.assoc (Limits.pullback.snd P.hom (prod.map g g)) prod.fst g).symm).trans
      (congrArg (fun k ↦ k ≫ g)
        (rfl : Limits.pullback.snd P.hom (prod.map g g) ≫ prod.fst = (P.pullback g).t)))

/-- The first pullback projection intertwines the source maps of a restriction. -/
private theorem restrict_s_comp {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) :
    Limits.pullback.fst P.hom (prod.map g g) ≫ P.s = (P.pullback g).s ≫ g :=
  ((congrArg (fun k ↦ Limits.pullback.fst P.hom (prod.map g g) ≫ k)
      (rfl : P.s = P.hom ≫ prod.snd)).trans
    (Limits.pullback.condition_assoc (prod.snd : U ⨯ U ⟶ U))).trans
    (((congrArg (fun k ↦ Limits.pullback.snd P.hom (prod.map g g) ≫ k) (prod.map_snd g g)).trans
        (Category.assoc (Limits.pullback.snd P.hom (prod.map g g)) prod.snd g).symm).trans
      (congrArg (fun k ↦ k ≫ g)
        (rfl : Limits.pullback.snd P.hom (prod.map g g) ≫ prod.snd = (P.pullback g).s)))

/-- The first pullback projection intertwines the target maps on underlying algebraic spaces. -/
private theorem restrict_t_comp_left {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) :
    (Limits.pullback.fst P.hom (prod.map g g)).left ≫ P.t.left =
      (P.pullback g).t.left ≫ g.left :=
  ((Over.comp_left _ _ _ (Limits.pullback.fst P.hom (prod.map g g)) P.t).symm.trans
    (congrArg Over.Hom.left (P.restrict_t_comp g))).trans
    (Over.comp_left _ _ _ (P.pullback g).t g)

/-- The first pullback projection intertwines the source maps on underlying algebraic spaces. -/
private theorem restrict_s_comp_left {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) :
    (Limits.pullback.fst P.hom (prod.map g g)).left ≫ P.s.left =
      (P.pullback g).s.left ≫ g.left :=
  ((Over.comp_left _ _ _ (Limits.pullback.fst P.hom (prod.map g g)) P.s).symm.trans
    (congrArg Over.Hom.left (P.restrict_s_comp g))).trans
    (Over.comp_left _ _ _ (P.pullback g).s g)

/-- The first pullback projection intertwines target maps on scheme-valued points. -/
private theorem restrict_t_comp_app {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) (T : Over S) :
    (Limits.pullback.fst P.hom (prod.map g g)).left.app (op T) ≫ P.t.left.app (op T) =
      (P.pullback g).t.left.app (op T) ≫ g.left.app (op T) :=
  ((NatTrans.comp_app (Limits.pullback.fst P.hom (prod.map g g)).left P.t.left (op T)).symm.trans
    (NatTrans.congr_app (P.restrict_t_comp_left g) (op T))).trans
    (NatTrans.comp_app (P.pullback g).t.left g.left (op T))

/-- The first pullback projection intertwines source maps on scheme-valued points. -/
private theorem restrict_s_comp_app {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) (T : Over S) :
    (Limits.pullback.fst P.hom (prod.map g g)).left.app (op T) ≫ P.s.left.app (op T) =
      (P.pullback g).s.left.app (op T) ≫ g.left.app (op T) :=
  ((NatTrans.comp_app (Limits.pullback.fst P.hom (prod.map g g)).left P.s.left (op T)).symm.trans
    (NatTrans.congr_app (P.restrict_s_comp_left g) (op T))).trans
    (NatTrans.comp_app (P.pullback g).s.left g.left (op T))

/-- Applying `g` to the target projection of a restricted relation recovers the original
target projection of the first pullback projection. -/
private theorem restrict_t_app {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) {T : Over S}
    (r : (P.pullback g).left.left.functorOfPoints.obj (op T)) :
    P.t.left.app (op T) ((Limits.pullback.fst P.hom (prod.map g g)).left.app (op T) r) =
      g.left.app (op T) ((P.pullback g).t.left.app (op T) r) :=
  (Eq.symm
      (CategoryTheory.comp_apply
        ((Limits.pullback.fst P.hom (prod.map g g)).left.app (op T))
        (P.t.left.app (op T)) r)).trans
    ((ConcreteCategory.congr_hom (P.restrict_t_comp_app g T) r).trans
      (CategoryTheory.comp_apply
        ((P.pullback g).t.left.app (op T)) (g.left.app (op T)) r))

/-- Applying `g` to the source projection of a restricted relation recovers the original
source projection of the first pullback projection. -/
private theorem restrict_s_app {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) {T : Over S}
    (r : (P.pullback g).left.left.functorOfPoints.obj (op T)) :
    P.s.left.app (op T) ((Limits.pullback.fst P.hom (prod.map g g)).left.app (op T) r) =
      g.left.app (op T) ((P.pullback g).s.left.app (op T) r) :=
  (Eq.symm
      (CategoryTheory.comp_apply
        ((Limits.pullback.fst P.hom (prod.map g g)).left.app (op T))
        (P.s.left.app (op T)) r)).trans
    ((ConcreteCategory.congr_hom (P.restrict_s_comp_app g T) r).trans
      (CategoryTheory.comp_apply
        ((P.pullback g).s.left.app (op T)) (g.left.app (op T)) r))

/-- Related scheme-valued points of a restriction remain related after applying `g`. -/
private theorem restrict_schemePointRel {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) {T : Over S}
    {x y : U'.left.functorOfPoints.obj (op T)}
    (h : (P.pullback g).schemePointRel T x y) :
    P.schemePointRel T (g.left.app (op T) x) (g.left.app (op T) y) :=
  match h with
  | ⟨r, hx, hy⟩ =>
    ⟨(Limits.pullback.fst P.hom (prod.map g g)).left.app (op T) r,
      (P.restrict_t_app g r).trans (congrArg (g.left.app (op T)) hx),
      (P.restrict_s_app g r).trans (congrArg (g.left.app (op T)) hy)⟩

/-- The maps on quotient classes induced by a morphism commute with restriction
along morphisms of schemes over the base. -/
theorem quotientPresheafMap_naturality {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U U' : Over B} (P : PreRelation U) (g : U' ⟶ U)
    {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    (P.pullback g).quotientPresheaf.map f ≫
        TypeCat.ofHom (Quot.map (g.left.app T') fun _ _ h ↦ by exact restrict_schemePointRel P g h) =
      TypeCat.ofHom (Quot.map (g.left.app T) fun _ _ h ↦ by exact restrict_schemePointRel P g h) ≫
        P.quotientPresheaf.map f :=
  sorry

/-- The map of quotient presheaves induced by restriction of a pre-relation along `g`. -/
def quotientPresheafMap {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) :
    (P.pullback g).quotientPresheaf ⟶ P.quotientPresheaf where
  app T :=
    TypeCat.ofHom <|
      Quot.map (g.left.app T) fun _ _ h ↦ by exact restrict_schemePointRel P g h
  naturality {_ _} f := P.quotientPresheafMap_naturality g f

/-- The restriction-induced quotient presheaf map sends the class of a point to the
class of its image under `g`. -/
theorem quotientPresheafMap_mk {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) (T : Over S)
    (a : U'.left.functorOfPoints.obj (op T)) :
    (P.quotientPresheafMap g).app (op T) (Quot.mk ((P.pullback g).schemePointRel T) a) =
      Quot.mk (P.schemePointRel T) (g.left.app (op T) a) :=
  sorry

/-- The map of fppf quotient sheaves `U'/R' ⟶ U/R` induced by restriction along `g`. -/
def quotientSheafMap {S : Scheme.{u}} {B : AlgebraicSpace S} {U U' : Over B}
    (P : PreRelation U) (g : U' ⟶ U) :
    (P.pullback g).quotientSheaf ⟶ P.quotientSheaf :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
    (Functor.whiskerRight (P.quotientPresheafMap g) uliftFunctor.{u + 1, u})

/-- The restriction-induced quotient sheaf map sends the class of a point of `U'` to
the class of its image under `g`. -/
theorem quotientSheafMap_quotientClass {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U U' : Over B} (P : PreRelation U) (g : U' ⟶ U) (T : Over S)
    (a : U'.left.functorOfPoints.obj (op T)) :
    (P.quotientSheafMap g).hom.app (op T) ((P.pullback g).quotientClass T a) =
      P.quotientClass T (g.left.app (op T) a) :=
  sorry

/-- The quotient projections form a commutative square with the restriction-induced
quotient sheaf map. -/
theorem quotientMap_comp_quotientSheafMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U U' : Over B} (P : PreRelation U) (g : U' ⟶ U) :
    (P.pullback g).quotientMap ≫ P.quotientSheafMap g =
      toSheaf.map g.left ≫ P.quotientMap :=
  sorry

/-- Restricting a pre-equivalence relation induces an injective map of fppf quotient sheaves. -/
theorem quotientSheafMap_isLocallyInjective {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U U' : Over B} (P : PreRelation U) (g : U' ⟶ U) (hP : P.IsPreEquivalence) :
    Sheaf.IsLocallyInjective (P.quotientSheafMap g) :=
  sorry

/-- A morphism surjective as a map of fppf sheaves induces an isomorphism on the
quotient sheaves of a pre-equivalence relation and its restriction. -/
theorem quotientSheafMap_isIso_of_locallySurjective {S : Scheme.{u}}
    {B : AlgebraicSpace S} {U U' : Over B} (P : PreRelation U) (g : U' ⟶ U)
    (hP : P.IsPreEquivalence)
    (hg : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) g.left) :
    IsIso (P.quotientSheafMap g) :=
  sorry

/-- A singleton fppf covering induces an isomorphism on the quotient sheaves of a
pre-equivalence relation and its restriction. -/
theorem quotientSheafMap_isIso_of_fppfCovering {S : Scheme.{u}}
    {B : AlgebraicSpace S} {U U' : Over B} (P : PreRelation U) (g : U' ⟶ U)
    (hP : P.IsPreEquivalence)
    [FppfCovering (fun _ : PUnit ↦ U'.left) (fun _ ↦ g.left)] :
    IsIso (P.quotientSheafMap g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
