module

public import ReasLib.Algebra.PolynomialTower
public import ReasLib.AlgebraicGeometry.RingedSite.PolynomialAugmentation
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.CategoryTheory.Sites.Chaotic

/-!
# Ringed topoi of polynomial squares

The three opposite polynomial-tower functors restrict the corresponding
structure sheaves and induce morphisms of ringed topoi.
-/

@[expose] public section

open CategoryTheory Opposite
open CommAlgCat.Over.Polynomial

noncomputable section

universe u

namespace RingedSite.Cotangent.PolynomialTower

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- The opposite category of polynomial squares over `A → B → C`. -/
abbrev site := (Algebra.PolynomialTower A B C)ᵒᵖ

/-- The first opposite projection sends a polynomial square to its first augmented algebra. -/
def u1 : site A B C ⥤ Algebra.PolynomialSite A B :=
  (Algebra.PolynomialTower.forgetToBase A B C).op

/-- The second opposite projection views the second augmented algebra over `A`. -/
def u2 : site A B C ⥤ Algebra.PolynomialSite A C :=
  (Algebra.PolynomialTower.forgetToOverA A B C).op

/-- The third opposite projection tensors the second algebra with `B` over the first. -/
def u3 : site A B C ⥤ Algebra.PolynomialSite B C :=
  (Algebra.PolynomialTower.forgetToOverB A B C).op

/-- The first opposite projection evaluates to the opposite first augmented algebra. -/
theorem u1_obj (X : Algebra.PolynomialTower A B C) :
    (u1 A B C).obj (op X) = op (Algebra.PolynomialTower.base X) := rfl

/-- The second opposite projection evaluates to the opposite second augmented algebra. -/
theorem u2_obj (X : Algebra.PolynomialTower A B C) :
    (u2 A B C).obj (op X) = op (Algebra.PolynomialTower.overA X) := rfl

/-- The third opposite projection evaluates to the opposite tensor augmentation. -/
theorem u3_obj (X : Algebra.PolynomialTower A B C) :
    (u3 A B C).obj (op X) = op (Algebra.PolynomialTower.tensorOverBase X) := rfl

/-- The first opposite projection acts by the opposite first component on morphisms. -/
theorem u1_map {X Y : Algebra.PolynomialTower A B C} (f : X ⟶ Y) :
    (u1 A B C).map f.op = ((Algebra.PolynomialTower.forgetToBase A B C).map f).op := rfl

/-- The second opposite projection acts by the opposite second component on morphisms. -/
theorem u2_map {X Y : Algebra.PolynomialTower A B C} (f : X ⟶ Y) :
    (u2 A B C).map f.op = ((Algebra.PolynomialTower.forgetToOverA A B C).map f).op := rfl

/-- The third opposite projection acts by the opposite tensor map on morphisms. -/
theorem u3_map {X Y : Algebra.PolynomialTower A B C} (f : X ⟶ Y) :
    (u3 A B C).map f.op = ((Algebra.PolynomialTower.forgetToOverB A B C).map f).op := rfl

/-- Type-valued presheaves admit pointwise right Kan extension along the first projection. -/
instance u1_op_hasPointwiseRightKanExtension
    (F : (site A B C)ᵒᵖ ⥤ Type (u + 1)) :
    (u1 A B C).op.HasPointwiseRightKanExtension F := sorry

/-- Type-valued presheaves admit pointwise right Kan extension along the second projection. -/
instance u2_op_hasPointwiseRightKanExtension
    (F : (site A B C)ᵒᵖ ⥤ Type (u + 1)) :
    (u2 A B C).op.HasPointwiseRightKanExtension F := sorry

/-- Type-valued presheaves admit pointwise right Kan extension along the tensor projection. -/
instance u3_op_hasPointwiseRightKanExtension
    (F : (site A B C)ᵒᵖ ⥤ Type (u + 1)) :
    (u3 A B C).op.HasPointwiseRightKanExtension F := sorry

/-- The lifted first structure sheaf is the restriction of the polynomial structure sheaf. -/
def structureSheaf1 : Sheaf (⊥ : GrothendieckTopology (site A B C)) CommRingCat.{u + 1} :=
  ((u1 A B C).sheafPushforwardContinuous CommRingCat.{u + 1} ⊥ ⊥).obj
    (Site.structureSheafLift A B)

/-- The lifted second structure sheaf is the restriction from the polynomial site over `A`. -/
def structureSheaf2 : Sheaf (⊥ : GrothendieckTopology (site A B C)) CommRingCat.{u + 1} :=
  ((u2 A B C).sheafPushforwardContinuous CommRingCat.{u + 1} ⊥ ⊥).obj
    (Site.structureSheafLift A C)

/-- The lifted tensor structure sheaf is the restriction from the polynomial site over `B`. -/
def structureSheaf3 : Sheaf (⊥ : GrothendieckTopology (site A B C)) CommRingCat.{u + 1} :=
  ((u3 A B C).sheafPushforwardContinuous CommRingCat.{u + 1} ⊥ ⊥).obj
    (Site.structureSheafLift B C)

/-- The polynomial-square site with the lifted first source-ring sheaf. -/
def ringedSite1 : RingedSite.{u + 1, u, u + 1} :=
  ofCommRingSheaf ⊥ (structureSheaf1 A B C)

/-- The polynomial-square site with the lifted second source-ring sheaf. -/
def ringedSite2 : RingedSite.{u + 1, u, u + 1} :=
  ofCommRingSheaf ⊥ (structureSheaf2 A B C)

/-- The polynomial-square site with the lifted tensor source-ring sheaf. -/
def ringedSite3 : RingedSite.{u + 1, u, u + 1} :=
  ofCommRingSheaf ⊥ (structureSheaf3 A B C)

/-- The first structure sheaf evaluates to the lifted first polynomial ring. -/
theorem structureSheaf1_obj (X : Algebra.PolynomialTower A B C) :
    (structureSheaf1 A B C).obj.obj (op (op X)) =
      uliftCommRing.obj (CommRingCat.of (Algebra.PolynomialTower.P X)) := rfl

/-- The second structure sheaf evaluates to the lifted second polynomial ring. -/
theorem structureSheaf2_obj (X : Algebra.PolynomialTower A B C) :
    (structureSheaf2 A B C).obj.obj (op (op X)) =
      uliftCommRing.obj (CommRingCat.of (Algebra.PolynomialTower.Q X)) := rfl

/-- The third structure sheaf evaluates to the lifted tensor base change. -/
theorem structureSheaf3_obj (X : Algebra.PolynomialTower A B C) :
    (structureSheaf3 A B C).obj.obj (op (op X)) =
      uliftCommRing.obj (CommRingCat.of (Algebra.PolynomialTower.tensorOverBase X).obj.left) := rfl

/-- The first structure sheaf acts on a map of squares by the lifted first ring map. -/
theorem structureSheaf1_map {X Y : Algebra.PolynomialTower A B C} (f : X ⟶ Y) :
    (structureSheaf1 A B C).obj.map f.op.op =
      uliftCommRing.map (CommRingCat.ofHom (Algebra.PolynomialTower.mapP f).hom.toRingHom) := rfl

/-- The second structure sheaf acts on a map of squares by the lifted second ring map. -/
theorem structureSheaf2_map {X Y : Algebra.PolynomialTower A B C} (f : X ⟶ Y) :
    (structureSheaf2 A B C).obj.map f.op.op =
      uliftCommRing.map (CommRingCat.ofHom (Algebra.PolynomialTower.mapQ f).hom.toRingHom) := rfl

/-- The third structure sheaf acts on a map of squares by the lifted tensor ring map. -/
theorem structureSheaf3_map {X Y : Algebra.PolynomialTower A B C} (f : X ⟶ Y) :
    (structureSheaf3 A B C).obj.map f.op.op =
      uliftCommRing.map (CommRingCat.ofHom
        ((Algebra.PolynomialTower.forgetToOverB A B C).map f).hom.left.hom.toRingHom) := rfl

/-- The first opposite projection induces a morphism of ringed topoi. -/
def toBase : ToposHom (ringedSite1 A B C) (Site.ringedSite A B) :=
  Cocontinuous.toRingedTopos
    (X := ofCommRingSheaf (⊥ : GrothendieckTopology (site A B C)) (structureSheaf1 A B C))
    (Y := ofCommRingSheaf (Site.topology A B) (Site.structureSheafLift A B))
    (u1 A B C) (𝟙 _)

/-- The second opposite projection induces a morphism of ringed topoi over `A`. -/
def toOverA : ToposHom (ringedSite2 A B C) (Site.ringedSite A C) :=
  Cocontinuous.toRingedTopos
    (X := ofCommRingSheaf (⊥ : GrothendieckTopology (site A B C)) (structureSheaf2 A B C))
    (Y := ofCommRingSheaf (Site.topology A C) (Site.structureSheafLift A C))
    (u2 A B C) (𝟙 _)

/-- The opposite tensor projection induces a morphism of ringed topoi over `B`. -/
def toOverB : ToposHom (ringedSite3 A B C) (Site.ringedSite B C) :=
  Cocontinuous.toRingedTopos
    (X := ofCommRingSheaf (⊥ : GrothendieckTopology (site A B C)) (structureSheaf3 A B C))
    (Y := ofCommRingSheaf (Site.topology B C) (Site.structureSheafLift B C))
    (u3 A B C) (𝟙 _)

/-- The first inverse-image structure map is bijective on every component. -/
theorem toBase_structureMap_bijective (U : (site A B C)ᵒᵖ) :
    Function.Bijective ((toBase A B C).structureMap.hom.app U) := sorry

/-- The second inverse-image structure map is bijective on every component. -/
theorem toOverA_structureMap_bijective (U : (site A B C)ᵒᵖ) :
    Function.Bijective ((toOverA A B C).structureMap.hom.app U) := sorry

/-- The tensor inverse-image structure map is bijective on every component. -/
theorem toOverB_structureMap_bijective (U : (site A B C)ᵒᵖ) :
    Function.Bijective ((toOverB A B C).structureMap.hom.app U) := sorry

end RingedSite.Cotangent.PolynomialTower
