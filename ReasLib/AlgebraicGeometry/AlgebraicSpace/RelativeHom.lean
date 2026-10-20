module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Basic

/-!
# Postcomposition and identity sections of relative morphisms

Relative-morphism sheaves admit postcomposition and identity sections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Z X B : AlgebraicSpace S}

/-- Postcomposition preserves the triangle over the base. -/
theorem postcomp_w (f : X ⟶ Z) (g : Z ⟶ B) {T : Over S}
    (p : Pair g (f ≫ g) T) :
    (BaseChangeMorphism.toMap p.b ≫ f) ≫ g = pullback.fst p.a g ≫ p.a :=
  (Category.assoc (BaseChangeMorphism.toMap p.b) f g).trans
    (BaseChangeMorphism.toMap_comm p.b)

/-- Postcompose a relative morphism with a morphism to `Z`. -/
def postcompPoint (f : X ⟶ Z) (g : Z ⟶ B) {T : Over S}
    (p : Pair g (f ≫ g) T) : Pair g g T :=
  mk p.a (BaseChangeMorphism.ofMap
    (BaseChangeMorphism.toMap p.b ≫ f) (postcomp_w f g p))

/-- Postcomposition commutes with restriction to test schemes. -/
theorem postcomp_naturality (f : X ⟶ Z) (g : Z ⟶ B)
    {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') :
    (presheaf g (f ≫ g)).map φ ≫ TypeCat.ofHom (postcompPoint f g) =
      TypeCat.ofHom (postcompPoint f g) ≫ (presheaf g g).map φ := sorry

/-- The sheaf morphism induced by postcomposition with `f`. -/
def postcomp (f : X ⟶ Z) (g : Z ⟶ B) : sheaf g (f ≫ g) ⟶ sheaf g g :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom (postcompPoint f g)
      naturality := fun _ _ φ ↦ postcomp_naturality f g φ }

/-- The components of postcomposition are given by postcomposition of pairs. -/
theorem postcomp_app (f : X ⟶ Z) (g : Z ⟶ B) (T : (Over S)ᵒᵖ) :
    (postcomp f g).hom.app T =
      TypeCat.ofHom fun (p : Pair g (f ≫ g) T.unop) ↦ postcompPoint f g p := rfl

/-- The identity of the base change of `Z` defines a relative endomorphism. -/
def idSectionPoint (g : Z ⟶ B) {T : Over S} (a : ofOver T ⟶ B) : Pair g g T :=
  mk a (𝟙 (Over.mk (pullback.fst a g)))

/-- A point of `B` determines the identity of the corresponding base change of `Z`. -/
def idSectionApp (g : Z ⟶ B) (T : (Over S)ᵒᵖ)
    (x : (toSheaf.obj B).obj.obj T) : Pair g g T.unop :=
  idSectionPoint g (yonedaEquiv.symm x.down)

/-- The identity section commutes with restriction to test schemes. -/
theorem idSection_naturality (g : Z ⟶ B) {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') :
    (toSheaf.obj B).obj.map φ ≫ TypeCat.ofHom (idSectionApp g T') =
      TypeCat.ofHom (idSectionApp g T) ≫ (presheaf g g).map φ := sorry

/-- The identity section from `B` to its relative-endomorphism sheaf of `Z`. -/
def idSection (g : Z ⟶ B) : toSheaf.obj B ⟶ sheaf g g :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom (idSectionApp g T)
      naturality := fun _ _ φ ↦ idSection_naturality g φ }

/-- The components of the identity section are the identity pairs. -/
theorem idSection_app (g : Z ⟶ B) (T : (Over S)ᵒᵖ) :
    (idSection g).hom.app T = TypeCat.ofHom (idSectionApp g T) := rfl

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
