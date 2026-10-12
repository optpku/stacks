/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
  sorry

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
  sorry

/-- Naturality of `quotientSheafLiftApp`. -/
theorem quotientSheafLiftApp_naturality {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))}
    (q : toSheaf.obj U.left ⟶ F)
    (h_eq : toSheaf.map P.t.left ≫ q = toSheaf.map P.s.left ≫ q)
    ⦃T T' : (Over S)ᵒᵖ⦄ (f : T ⟶ T') :
    (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}).map f ≫
        P.quotientSheafLiftApp q h_eq T' =
      P.quotientSheafLiftApp q h_eq T ≫ F.obj.map f :=
  sorry

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
  sorry

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
  sorry

/-- A morphism that factors through the quotient sheaf is invariant. -/
theorem isInvariantHom_of_factors {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (φ : U ⟶ X)
    (ψ : P.quotientSheaf ⟶ toSheaf.obj X.left)
    (hψ : P.quotientMap ≫ ψ = toSheaf.map φ.left) :
    P.IsInvariantHom φ :=
  sorry

/-- A morphism `φ : U ⟶ X` over `B` is invariant under `P` if and only if it factors
through the fppf quotient sheaf `U/R`. -/
theorem isInvariantHom_iff_factors {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) :
    P.IsInvariantHom φ ↔
      ∃ ψ : P.quotientSheaf ⟶ toSheaf.obj X.left,
        P.quotientMap ≫ ψ = toSheaf.map φ.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
