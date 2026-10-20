module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage

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

/-- The structured arrow presenting `U ⟶ X ×_Y V` in the right Kan extension diagram of a sheaf
on `X_étale`. -/
def EtaleSquare.toStructuredArrow (sq : EtaleSquare f) :
    StructuredArrow (op ((etaleBaseChange f).obj sq.right)) (smallEtaleToSpaces X).op :=
  StructuredArrow.mk (Y := op sq.left) (EtaleTopos.squareArrow f sq).op

/-- The right object of `EtaleSquare.toStructuredArrow` is the left vertex of the square. -/
@[simp]
theorem EtaleSquare.toStructuredArrow_right (sq : EtaleSquare f) :
    sq.toStructuredArrow.right = op sq.left :=
  rfl

/-- The Ran diagram of a sheaf of sets on `X_étale` at the fibre product `X ×_Y V`. -/
abbrev pushforwardRanDiagram (f : X ⟶ Y) (ℱ : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    (V : smallEtaleSite Y) :
    StructuredArrow (op ((etaleBaseChange f).obj V)) (smallEtaleToSpaces X).op ⥤ Type (u + 1) :=
  StructuredArrow.proj (op ((etaleBaseChange f).obj V)) (smallEtaleToSpaces X).op ⋙ ℱ.obj

variable {𝒢 : Sheaf (smallEtaleTopology Y) (Type (u + 1))}
variable {ℱ : Sheaf (smallEtaleTopology X) (Type (u + 1))}

namespace FMap

/-- The component `𝒢(V) ⟶ ℱ(U)` of a morphism `𝒢 ⟶ f_small,* ℱ` on an `f`-square, obtained by
restricting the pushforward sections at `X ×_Y V` along `U ⟶ X ×_Y V`. -/
def ofPushforwardHom_app (α : 𝒢 ⟶ (sheafPushforwardType f).obj ℱ) (sq : EtaleSquare f) :
    𝒢.obj.obj (op sq.right) ⟶ ℱ.obj.obj (op sq.left) :=
  α.hom.app (op sq.right) ≫
    ((smallEtaleToSpaces X).op.ranObjObjIsoLimit ℱ.obj
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
    ((smallEtaleToSpaces X).op.ranObjObjIsoLimit ℱ.obj
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

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable (𝒢 : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
variable (ℱ : Sheaf (smallEtaleTopology X) (Type (u + 1)))

/-- Morphisms into small étale pushforward are canonically equivalent to restriction-compatible
`f`-maps of sheaves of sets. -/
def fMapHomEquiv : (𝒢 ⟶ (sheafPushforwardType f).obj ℱ) ≃ FMap f 𝒢 ℱ where
  toFun := FMap.ofPushforwardHom
  invFun := FMap.toPushforwardHom
  left_inv := FMap.toPushforwardHom_ofPushforwardHom
  right_inv := FMap.ofPushforwardHom_toPushforwardHom

/-- `fMapHomEquiv` sends a morphism `𝒢 ⟶ f_small,* ℱ` to the `f`-map with components
`FMap.ofPushforwardHom_app`. -/
@[simp]
theorem fMapHomEquiv_apply (α : 𝒢 ⟶ (sheafPushforwardType f).obj ℱ) (sq : EtaleSquare f) :
    (fMapHomEquiv f 𝒢 ℱ α).app sq = FMap.ofPushforwardHom_app α sq :=
  rfl

/-- The inverse of `fMapHomEquiv` is `FMap.toPushforwardHom`. -/
@[simp]
theorem fMapHomEquiv_symm_apply (φ : FMap f 𝒢 ℱ) :
    (fMapHomEquiv f 𝒢 ℱ).symm φ = FMap.toPushforwardHom φ :=
  rfl

/-- Maps `f_small^{-1} 𝒢 ⟶ ℱ` are canonically equivalent to `f`-maps `φ : 𝒢 ⟶ ℱ`. -/
def fMapInverseImageHomEquiv :
    ((sheafTypeInverseImage f).obj 𝒢 ⟶ ℱ) ≃ FMap f 𝒢 ℱ :=
  ((sheafAdjunctionType f).homEquiv 𝒢 ℱ).trans (fMapHomEquiv f 𝒢 ℱ)

/-- The inverse-image comparison is the hom-equivalence of inverse image left adjoint to
pushforward, followed by the pushforward comparison with `f`-maps. -/
theorem fMapInverseImageHomEquiv_eq :
    fMapInverseImageHomEquiv f 𝒢 ℱ =
      ((sheafAdjunctionType f).homEquiv 𝒢 ℱ).trans (fMapHomEquiv f 𝒢 ℱ) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace

