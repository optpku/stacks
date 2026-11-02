/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Invariant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf

/-!
# Descent through quotient sheaves of pre-relations

An equalizing morphism from the sheaf of points of an algebraic space descends to
the quotient sheaf of a pre-relation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- An equalizing sheaf map out of `U` identifies points related by the pre-relation. -/
theorem quotientSheafLift_respects {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))}
    (q : toSheaf.obj U.left ⟶ F)
    (h_eq : toSheaf.map P.t.left ≫ q = toSheaf.map P.s.left ≫ q)
    {T : (Over S)ᵒᵖ} {x y : U.left.functorOfPoints.obj T}
    (hxy : P.schemePointRel T.unop x y) :
    q.hom.app T (ULift.up x) = q.hom.app T (ULift.up y) :=
  by
    obtain ⟨r, hx, hy⟩ := hxy
    have h_eq' := congrArg (fun k : toSheaf.obj P.left.left ⟶ F => k.hom.app T) h_eq
    have h_eq'' := congrArg (fun k => k (ULift.up r)) h_eq'
    have h_eq''' :
        q.hom.app T (ULift.up (P.t.left.app T r)) =
          q.hom.app T (ULift.up (P.s.left.app T r)) := by
      change q.hom.app T (ULift.up (P.t.left.app T r)) =
        q.hom.app T (ULift.up (P.s.left.app T r)) at h_eq''
      exact h_eq''
    have hx' := congrArg ULift.up hx
    have hy' := congrArg ULift.up hy
    change ULift.up (P.t.left.app T r) = ULift.up x at hx'
    change ULift.up (P.s.left.app T r) = ULift.up y at hy'
    exact (congrArg (q.hom.app T) hx').symm.trans
      (h_eq'''.trans (congrArg (q.hom.app T) hy'))

/-- The pointwise map on universe-raised quotient classes induced by an equalizing
sheaf morphism out of `U`. -/
def quotientSheafLiftApp {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))}
    (q : toSheaf.obj U.left ⟶ F)
    (h_eq : toSheaf.map P.t.left ≫ q = toSheaf.map P.s.left ≫ q)
    (T : (Over S)ᵒᵖ) :
    (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}).obj T ⟶ F.obj.obj T :=
  TypeCat.ofHom fun (x : ULift (Quot (P.schemePointRel T.unop))) ↦
    Quot.lift (fun a ↦ q.hom.app T (ULift.up a))
      (fun _ _ hab ↦ P.quotientSheafLift_respects q h_eq hab) x.down

/-- Evaluation of `quotientSheafLiftApp` on a represented quotient class. -/
theorem quotientSheafLiftApp_apply {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))}
    (q : toSheaf.obj U.left ⟶ F)
    (h_eq : toSheaf.map P.t.left ≫ q = toSheaf.map P.s.left ≫ q)
    (T : (Over S)ᵒᵖ) (a : U.left.functorOfPoints.obj T) :
    P.quotientSheafLiftApp q h_eq T (ULift.up (Quot.mk (P.schemePointRel T.unop) a)) =
      q.hom.app T (ULift.up a) :=
  rfl

/-- Naturality of `quotientSheafLiftApp`. -/
theorem quotientSheafLiftApp_naturality {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))}
    (q : toSheaf.obj U.left ⟶ F)
    (h_eq : toSheaf.map P.t.left ≫ q = toSheaf.map P.s.left ≫ q)
    ⦃T T' : (Over S)ᵒᵖ⦄ (f : T ⟶ T') :
    (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}).map f ≫
        P.quotientSheafLiftApp q h_eq T' =
      P.quotientSheafLiftApp q h_eq T ≫ F.obj.map f :=
  by
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨x⟩
    refine Quot.inductionOn x ?_
    intro a
    change q.hom.app T' (ULift.up (U.left.functorOfPoints.map f a)) =
      F.obj.map f (q.hom.app T (ULift.up a))
    have hnat := NatTrans.naturality_apply q.hom f
      (ULift.up a : (toSheaf.obj U.left).obj.obj T)
    change q.hom.app T' (ULift.up (U.left.functorOfPoints.map f a)) =
      F.obj.map f (q.hom.app T (ULift.up a)) at hnat
    exact hnat

/-- The presheaf-level descent of an equalizing sheaf map along the quotient. -/
def quotientPresheafLift {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))}
    (q : toSheaf.obj U.left ⟶ F)
    (h_eq : toSheaf.map P.t.left ≫ q = toSheaf.map P.s.left ≫ q) :
    P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u} ⟶ F.obj where
  app T := P.quotientSheafLiftApp q h_eq T
  naturality := P.quotientSheafLiftApp_naturality q h_eq

/-- The component of `quotientPresheafLift` at `T` is `quotientSheafLiftApp`. -/
theorem quotientPresheafLift_app {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))}
    (q : toSheaf.obj U.left ⟶ F)
    (h_eq : toSheaf.map P.t.left ≫ q = toSheaf.map P.s.left ≫ q)
    (T : (Over S)ᵒᵖ) :
    (P.quotientPresheafLift q h_eq).app T = P.quotientSheafLiftApp q h_eq T :=
  rfl

/-- The unique sheaf morphism `U/R ⟶ F` induced by an equalizing map `U ⟶ F`. -/
def quotientSheafLift {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))}
    (q : toSheaf.obj U.left ⟶ F)
    (h_eq : toSheaf.map P.t.left ≫ q = toSheaf.map P.s.left ≫ q) :
    P.quotientSheaf ⟶ F :=
  ((sheafificationAdjunction (Scheme.fppfTopology.over S) (Type (u + 1))).homEquiv
      (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}) F).symm
    (P.quotientPresheafLift q h_eq)

/-- The quotient comparison factors the original equalizing map. -/
theorem quotientMap_comp_quotientSheafLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} (P : PreRelation U)
    {F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))}
    (q : toSheaf.obj U.left ⟶ F)
    (h_eq : toSheaf.map P.t.left ≫ q = toSheaf.map P.s.left ≫ q) :
    P.quotientMap ≫ P.quotientSheafLift q h_eq = q :=
  by
    apply Sheaf.hom_ext
    change
      (Functor.whiskerRight P.quotientMk uliftFunctor.{u + 1, u} ≫
          toSheafify (Scheme.fppfTopology.over S)
            (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})) ≫
        sheafifyLift (Scheme.fppfTopology.over S)
          (P.quotientPresheafLift q h_eq) F.property = q.hom
    rw [Category.assoc, toSheafify_sheafifyLift]
    ext T x
    rcases x with ⟨x⟩
    change P.quotientSheafLiftApp q h_eq T
        (ULift.up (Quot.mk (P.schemePointRel T.unop) x)) =
      q.hom.app T (ULift.up x)
    rw [quotientSheafLiftApp_apply]

/-- A morphism that factors through the quotient sheaf is invariant. -/
theorem isInvariantHom_of_factors {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (φ : U ⟶ X)
    (ψ : P.quotientSheaf ⟶ toSheaf.obj X.left)
    (hψ : P.quotientMap ≫ ψ = toSheaf.map φ.left) :
    P.IsInvariantHom φ :=
  by
    change P.t ≫ φ = P.s ≫ φ
    apply Over.OverMorphism.ext
    change P.t.left ≫ φ.left = P.s.left ≫ φ.left
    apply NatTrans.ext
    funext T
    apply ConcreteCategory.hom_ext
    intro x
    change φ.left.app T (P.t.left.app T x) = φ.left.app T (P.s.left.app T x)
    have hquot :
        P.quotientMap.hom.app T (ULift.up (P.t.left.app T x)) =
          P.quotientMap.hom.app T (ULift.up (P.s.left.app T x)) := by
      change (toSheafify (Scheme.fppfTopology.over S)
          (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})).app T
            (ULift.up (Quot.mk (P.schemePointRel T.unop) (P.t.left.app T x))) =
        (toSheafify (Scheme.fppfTopology.over S)
          (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})).app T
            (ULift.up (Quot.mk (P.schemePointRel T.unop) (P.s.left.app T x)))
      exact congrArg ((toSheafify (Scheme.fppfTopology.over S)
          (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})).app T)
        (congrArg ULift.up (Quot.sound (show P.schemePointRel T.unop
          (P.t.left.app T x) (P.s.left.app T x) from ⟨x, rfl, rfl⟩)))
    have hψ' := congrArg (fun k => k.hom.app T) hψ
    have hψt := congrArg (fun k => k (ULift.up (P.t.left.app T x))) hψ'
    have hψs := congrArg (fun k => k (ULift.up (P.s.left.app T x))) hψ'
    change ψ.hom.app T (P.quotientMap.hom.app T (ULift.up (P.t.left.app T x))) =
      ULift.up (φ.left.app T (P.t.left.app T x)) at hψt
    change ψ.hom.app T (P.quotientMap.hom.app T (ULift.up (P.s.left.app T x))) =
      ULift.up (φ.left.app T (P.s.left.app T x)) at hψs
    exact congrArg ULift.down
      (hψt.symm.trans ((congrArg (ψ.hom.app T) hquot).trans hψs))

/-- A morphism `φ : U ⟶ X` over `B` is invariant under `P` if and only if it factors
through the fppf quotient sheaf `U/R`. -/
theorem isInvariantHom_iff_factors {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) :
    P.IsInvariantHom φ ↔
      ∃ ψ : P.quotientSheaf ⟶ toSheaf.obj X.left,
        P.quotientMap ≫ ψ = toSheaf.map φ.left :=
  by
    constructor
    · intro hφ
      change P.t ≫ φ = P.s ≫ φ at hφ
      have h_eq : toSheaf.map P.t.left ≫ toSheaf.map φ.left =
          toSheaf.map P.s.left ≫ toSheaf.map φ.left := by
        rw [← toSheaf.map_comp, ← toSheaf.map_comp]
        exact congrArg (fun k : P.left ⟶ X => toSheaf.map k.left) hφ
      exact ⟨P.quotientSheafLift (toSheaf.map φ.left) h_eq,
        P.quotientMap_comp_quotientSheafLift (toSheaf.map φ.left) h_eq⟩
    · rintro ⟨ψ, hψ⟩
      exact P.isInvariantHom_of_factors φ ψ hψ

end AlgebraicGeometry.AlgebraicSpace.PreRelation
