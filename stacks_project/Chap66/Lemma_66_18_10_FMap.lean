/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward

/-!
# Comparison of `f`-maps with small étale pushforward

An `f`-map of sheaves of sets is determined by, and determines, a morphism into the small étale
pushforward, by evaluating the right Kan extension of `ℱ` at the fibre product `X ×_Y V`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}

/-- The morphism of functors of points `U ⟶ X ×_Y V` induced by an `f`-square. -/
def EtaleSquare.liftToBaseChange (sq : EtaleSquare f) :
    ofOver sq.left.left ⟶ etaleBaseChangeSpace f sq.right :=
  pullback.lift (f := homFunctor f) (g := homFunctor sq.right.hom)
    sq.left.hom (ofOverMap sq.map) sq.w

/-- The first projection of `EtaleSquare.liftToBaseChange` is the structure morphism of `U`. -/
theorem EtaleSquare.liftToBaseChange_fst (sq : EtaleSquare f) :
    sq.liftToBaseChange ≫ etaleBaseChangeHom f sq.right = sq.left.hom :=
  pullback.lift_fst (f := homFunctor f) (g := homFunctor sq.right.hom) _ _ _

/-- An `f`-square determines a morphism `U ⟶ X ×_Y V` in the étale site of algebraic spaces
over `X`. -/
def EtaleSquare.toOverHom (sq : EtaleSquare f) :
    (smallEtaleInclusion X).obj sq.left ⟶ (etaleBaseChange f).obj sq.right :=
  MorphismProperty.Over.homMk sq.liftToBaseChange sq.liftToBaseChange_fst

/-- The underlying morphism of algebraic spaces of `EtaleSquare.toOverHom` is the fibre-product
lift. -/
@[simp]
theorem EtaleSquare.toOverHom_left (sq : EtaleSquare f) :
    sq.toOverHom.left = sq.liftToBaseChange :=
  rfl

/-- The structured arrow presenting `U ⟶ X ×_Y V` in the right Kan extension diagram of a sheaf
on `X_étale`. -/
def EtaleSquare.toStructuredArrow (sq : EtaleSquare f) :
    StructuredArrow (op ((etaleBaseChange f).obj sq.right)) (smallEtaleInclusion X).op :=
  StructuredArrow.mk (Y := op sq.left) sq.toOverHom.op

/-- The right object of `EtaleSquare.toStructuredArrow` is the left vertex of the square. -/
@[simp]
theorem EtaleSquare.toStructuredArrow_right (sq : EtaleSquare f) :
    sq.toStructuredArrow.right = op sq.left :=
  rfl

/-- The Ran diagram of a sheaf of sets on `X_étale` at the fibre product `X ×_Y V`. -/
abbrev pushforwardRanDiagram (f : X ⟶ Y) (ℱ : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    (V : smallEtaleSite Y) :
    StructuredArrow (op ((etaleBaseChange f).obj V)) (smallEtaleInclusion X).op ⥤ Type (u + 1) :=
  StructuredArrow.proj (op ((etaleBaseChange f).obj V)) (smallEtaleInclusion X).op ⋙ ℱ.obj

/-- `pushforwardRanDiagram f ℱ V` is precomposition of `ℱ` with the structured-arrow projection at
`X ×_Y V`. -/
theorem pushforwardRanDiagram_eq (f : X ⟶ Y) (ℱ : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    (V : smallEtaleSite Y) :
    pushforwardRanDiagram f ℱ V =
      StructuredArrow.proj (op ((etaleBaseChange f).obj V)) (smallEtaleInclusion X).op ⋙ ℱ.obj :=
  rfl

variable {𝒢 : Sheaf (smallEtaleTopology Y) (Type (u + 1))}
variable {ℱ : Sheaf (smallEtaleTopology X) (Type (u + 1))}

namespace FMap

/-- The component `𝒢(V) ⟶ ℱ(U)` of a morphism `𝒢 ⟶ f_small,* ℱ` on an `f`-square, obtained by
restricting the pushforward sections at `X ×_Y V` along `U ⟶ X ×_Y V`. -/
def ofPushforwardHom_app (α : 𝒢 ⟶ (sheafPushforwardType f).obj ℱ) (sq : EtaleSquare f) :
    𝒢.obj.obj (op sq.right) ⟶ ℱ.obj.obj (op sq.left) :=
  α.hom.app (op sq.right) ≫
    ((smallEtaleInclusion X).op.ranObjObjIsoLimit ℱ.obj
      (op ((etaleBaseChange f).obj sq.right))).hom ≫
    limit.π (pushforwardRanDiagram f ℱ sq.right) sq.toStructuredArrow

/-- Restriction compatibility for the family of components extracted from a morphism
`𝒢 ⟶ f_small,* ℱ`. -/
theorem ofPushforwardHom_naturality (α : 𝒢 ⟶ (sheafPushforwardType f).obj ℱ)
    {sq sq' : EtaleSquare f} (i : sq'.left ⟶ sq.left) (j : sq'.right ⟶ sq.right)
    (hij : i.left ≫ sq.map = sq'.map ≫ j.left) :
    CommSq (𝒢.obj.map j.op) (ofPushforwardHom_app α sq) (ofPushforwardHom_app α sq')
      (ℱ.obj.map i.op) :=
  sorry

/-- The `f`-map associated to a morphism `𝒢 ⟶ f_small,* ℱ`. -/
def ofPushforwardHom (α : 𝒢 ⟶ (sheafPushforwardType f).obj ℱ) : FMap f 𝒢 ℱ where
  app := ofPushforwardHom_app α
  naturality := ofPushforwardHom_naturality α

/-- `ofPushforwardHom` evaluates on an `f`-square by restricting pushforward sections along
`U ⟶ X ×_Y V`. -/
@[simp]
theorem ofPushforwardHom_app_eq (α : 𝒢 ⟶ (sheafPushforwardType f).obj ℱ) (sq : EtaleSquare f) :
    (ofPushforwardHom α).app sq = ofPushforwardHom_app α sq :=
  rfl

/-- The cone of `f`-map components `𝒢(V) ⟶ ℱ(U)` indexed by morphisms `U ⟶ X ×_Y V` from schemes
étale over `X`. -/
def toPushforwardHomCone (φ : FMap f 𝒢 ℱ) (V : smallEtaleSite Y) :
    Cone (pushforwardRanDiagram f ℱ V) where
  pt := 𝒢.obj.obj (op V)
  π :=
    { app := fun a ↦ φ.app (etaleSquareOfArrow f V a)
      naturality := fun _ _ _ ↦ sorry }

/-- The vertex of `toPushforwardHomCone φ V` is the sections of `𝒢` at `V`. -/
@[simp]
theorem toPushforwardHomCone_pt (φ : FMap f 𝒢 ℱ) (V : smallEtaleSite Y) :
    (toPushforwardHomCone φ V).pt = 𝒢.obj.obj (op V) :=
  rfl

/-- The component at `V` of the morphism `𝒢 ⟶ f_small,* ℱ` associated to an `f`-map, as the
limit lift of the cone of square components. -/
def toPushforwardHom_app (φ : FMap f 𝒢 ℱ) (V : (smallEtaleSite Y)ᵒᵖ) :
    𝒢.obj.obj V ⟶ ((sheafPushforwardType f).obj ℱ).obj.obj V :=
  limit.lift (pushforwardRanDiagram f ℱ V.unop) (toPushforwardHomCone φ V.unop) ≫
    ((smallEtaleInclusion X).op.ranObjObjIsoLimit ℱ.obj
      (op ((etaleBaseChange f).obj V.unop))).inv

/-- Naturality of `toPushforwardHom_app` in objects of `Y_étale`. -/
theorem toPushforwardHom_naturality (φ : FMap f 𝒢 ℱ) {V W : (smallEtaleSite Y)ᵒᵖ} (j : V ⟶ W) :
    𝒢.obj.map j ≫ toPushforwardHom_app φ W =
      toPushforwardHom_app φ V ≫ ((sheafPushforwardType f).obj ℱ).obj.map j :=
  sorry

/-- The morphism `𝒢 ⟶ f_small,* ℱ` associated to an `f`-map. -/
def toPushforwardHom (φ : FMap f 𝒢 ℱ) : 𝒢 ⟶ (sheafPushforwardType f).obj ℱ :=
  ObjectProperty.homMk
    { app := fun V ↦ toPushforwardHom_app φ V
      naturality := fun _ _ j ↦ toPushforwardHom_naturality φ j }

/-- The underlying presheaf morphism of `toPushforwardHom φ` has components
`toPushforwardHom_app`. -/
@[simp]
theorem toPushforwardHom_hom_app (φ : FMap f 𝒢 ℱ) (V : (smallEtaleSite Y)ᵒᵖ) :
    (toPushforwardHom φ).hom.app V = toPushforwardHom_app φ V :=
  rfl

/-- Converting a morphism `𝒢 ⟶ f_small,* ℱ` to an `f`-map and back is the identity. -/
theorem toPushforwardHom_ofPushforwardHom (α : 𝒢 ⟶ (sheafPushforwardType f).obj ℱ) :
    toPushforwardHom (ofPushforwardHom α) = α :=
  sorry

/-- Converting an `f`-map to a morphism `𝒢 ⟶ f_small,* ℱ` and back is the identity. -/
theorem ofPushforwardHom_toPushforwardHom (φ : FMap f 𝒢 ℱ) :
    ofPushforwardHom (toPushforwardHom φ) = φ :=
  sorry

end FMap

end AlgebraicGeometry.AlgebraicSpace
