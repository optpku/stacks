module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Projections
public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeIsom.Automorphisms
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia.Group

/-!
# Pulled-back group law on relative automorphisms

The relative automorphism sheaf `Z ×_X I_{X/Y}` inherits a group-object
structure in the homotopy category of `SpacesOver Z.toGroupoids` by base
change of the unit, multiplication, and inversion of relative inertia.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.RelativeInertia
open AlgebraicGeometry.SpacesOver
open scoped Bicategory CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.RelativeIsom

/-- The identity-leg cone presenting the unit section `Z ⟶ Z ×_X I_{X/Y}`. -/
def unitCone {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    Bicategory.PseudoPullbackCone x (forget.{u + 1, u, u, u + 1} f) where
  pt := Z.toGroupoids
  fst := 𝟙 Z.toGroupoids
  snd := x ≫ identitySection.{u + 1, u, u, u + 1} f
  iso :=
    λ_ x ≪≫
      (ρ_ x).symm ≪≫
        whiskerLeftIso x
            (AlgebraicStack.RelativeInertia.identitySection_comp_forget_iso f).symm ≪≫
          (α_ x (identitySection.{u + 1, u, u, u + 1} f)
            (forget.{u + 1, u, u, u + 1} f)).symm

/-- The unit 1-morphism `Z ⟶ Isom_{X/Y}(x, x)` of the pulled-back group law. -/
def unitMap {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    Z.toGroupoids ⟶ relativeAut f x :=
  Bicategory.PseudoPullbackCone.lift (unitCone f x)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} x
      (forget.{u + 1, u, u, u + 1} f))

/-- The unit section followed by `fst` is isomorphic to the identity of `Z`. -/
def unitMap_fst {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    unitMap f x ≫ fst f x ≅ 𝟙 Z.toGroupoids :=
  Bicategory.PseudoPullbackCone.lift.fstIso (unitCone f x)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} x
      (forget.{u + 1, u, u, u + 1} f))

/-- The unit 1-morphism of relative automorphisms in `SpacesOver Z.toGroupoids`. -/
def oneHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    SpacesOver.id Z.toGroupoids ⟶ asSpacesOver f x :=
  SpacesOver.homMk (unitMap f x) (unitMap_fst f x).symm

/-- The underlying domain map of `oneHom f x` is `unitMap f x`. -/
theorem oneHom_left {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    SpacesOver.map (oneHom f x) = unitMap f x :=
  sorry

/-- The cospan transformation sending `Z ×_X I_{X/Y}` to `I_{X/Y} ×_X I_{X/Y}`
by the inertia projection on both legs. -/
def toInertiaPairCospan {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    CospanTransform (fst f x) (fst f x)
      (forget.{u + 1, u, u, u + 1} f) (forget.{u + 1, u, u, u + 1} f) :=
  CospanTransform.mk (snd f x) (snd f x) x
    (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} x
      (forget.{u + 1, u, u, u + 1} f)).symm
    (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} x
      (forget.{u + 1, u, u, u + 1} f)).symm

/-- The comparison ` (Z ×_X I_{X/Y}) ×_Z (Z ×_X I_{X/Y}) ⟶ I_{X/Y} ×_X I_{X/Y} `. -/
def toInertiaPair {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} (fst f x) (fst f x) ⟶
      AlgebraicStack.RelativeInertia.inertiaApex f :=
  TwoFibreProduct.map (toInertiaPairCospan f x)

/-- The 2-isomorphism witnessing that the pulled-back multiplication lands in
the cospan `x, forget f`. -/
def mulIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (fst f x) (fst f x) ≫
        fst f x) ≫ x ≅
      (toInertiaPair f x ≫ AlgebraicStack.RelativeInertia.composition f) ≫
        forget.{u + 1, u, u, u + 1} f :=
  α_ _ _ _ ≪≫
    whiskerLeftIso _
      (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} x
        (forget.{u + 1, u, u, u + 1} f)) ≪≫
      (α_ _ _ _).symm ≪≫
        whiskerRightIso
            (TwoFibreProduct.map.fstIso (toInertiaPairCospan f x)).symm _ ≪≫
          α_ _ _ _ ≪≫
            whiskerLeftIso _
                (AlgebraicStack.RelativeInertia.composition_comp_forget_iso f).symm ≪≫
              (α_ _ _ _).symm

/-- The multiplication cone of relative automorphisms over `Z`. -/
def mulCone {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    Bicategory.PseudoPullbackCone x (forget.{u + 1, u, u, u + 1} f) where
  pt := TwoFibreProduct.apex.{u + 1, u, u + 1, u} (fst f x) (fst f x)
  fst :=
    TwoFibreProduct.fst.{u + 1, u, u + 1, u} (fst f x) (fst f x) ≫ fst f x
  snd := toInertiaPair f x ≫ AlgebraicStack.RelativeInertia.composition f
  iso := mulIso f x

/-- Multiplication ` (Z ×_X I_{X/Y}) ×_Z (Z ×_X I_{X/Y}) ⟶ Z ×_X I_{X/Y} `. -/
def mulMap {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} (fst f x) (fst f x) ⟶
      relativeAut f x :=
  Bicategory.PseudoPullbackCone.lift (mulCone f x)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} x
      (forget.{u + 1, u, u, u + 1} f))

/-- Multiplication followed by `fst` recovers the structure morphism of the
binary product over `Z`. -/
def mulMap_fst {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    mulMap f x ≫ fst f x ≅
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} (fst f x) (fst f x) ≫
        fst f x :=
  Bicategory.PseudoPullbackCone.lift.fstIso (mulCone f x)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} x
      (forget.{u + 1, u, u, u + 1} f))

/-- The multiplication 1-morphism of relative automorphisms in
`SpacesOver Z.toGroupoids`. -/
def mulHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    tensor (asSpacesOver f x) (asSpacesOver f x) ⟶ asSpacesOver f x :=
  SpacesOver.homMk (mulMap f x) (mulMap_fst f x).symm

/-- The underlying domain map of `mulHom f x` is `mulMap f x`. -/
theorem mulHom_left {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    SpacesOver.map (mulHom f x) = mulMap f x :=
  sorry

/-- The cospan transformation of inversion, acting as the identity on `Z` and
as relative-inertia inversion on `I_{X/Y}`. -/
def invCospan {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    CospanTransform x (forget.{u + 1, u, u, u + 1} f) x
      (forget.{u + 1, u, u, u + 1} f) :=
  CospanTransform.mk (𝟙 Z.toGroupoids) (AlgebraicStack.RelativeInertia.inv f)
    (𝟙 X) (λ_ x ≪≫ (ρ_ x).symm)
    (AlgebraicStack.RelativeInertia.inv_comp_forget_iso f ≪≫
      (ρ_ (forget.{u + 1, u, u, u + 1} f)).symm)

/-- Inversion `Z ×_X I_{X/Y} ⟶ Z ×_X I_{X/Y}` as a 2-fibre-product map. -/
def invMap {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    relativeAut f x ⟶ relativeAut f x :=
  TwoFibreProduct.map (invCospan f x)

/-- Inversion followed by `fst` is isomorphic to `fst`. -/
def invMap_fst {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    invMap f x ≫ fst f x ≅ fst f x :=
  TwoFibreProduct.map.fstIso (invCospan f x) ≪≫ ρ_ (fst f x)

/-- The inversion 1-morphism of relative automorphisms in
`SpacesOver Z.toGroupoids`. -/
def invHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    asSpacesOver f x ⟶ asSpacesOver f x :=
  SpacesOver.homMk (invMap f x) (invMap_fst f x).symm

/-- The underlying domain map of `invHom f x` is `invMap f x`. -/
theorem invHom_left {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    SpacesOver.map (invHom f x) = invMap f x :=
  sorry

section GroupImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped MonoidalCategory

/-- The identity section is a left unit for multiplication. -/
private theorem Implementation.group_one_mul {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    (Bicategory.HomotopyCategory.mkHom (oneHom f x)) ▷ (asHomotopy f x) ≫ Bicategory.HomotopyCategory.mkHom (mulHom f x) = (λ_ (asHomotopy f x)).hom := sorry

/-- The identity section is a right unit for multiplication. -/
private theorem Implementation.group_mul_one {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    (asHomotopy f x) ◁ (Bicategory.HomotopyCategory.mkHom (oneHom f x)) ≫ Bicategory.HomotopyCategory.mkHom (mulHom f x) = (ρ_ (asHomotopy f x)).hom := sorry

/-- Multiplication of relative automorphisms is associative. -/
private theorem Implementation.group_mul_assoc {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    ((Bicategory.HomotopyCategory.mkHom (mulHom f x)) ▷ (asHomotopy f x)) ≫ Bicategory.HomotopyCategory.mkHom (mulHom f x) =
      (α_ (asHomotopy f x) (asHomotopy f x) (asHomotopy f x)).hom ≫ ((asHomotopy f x) ◁ (Bicategory.HomotopyCategory.mkHom (mulHom f x))) ≫ Bicategory.HomotopyCategory.mkHom (mulHom f x) := sorry

/-- Inversion is a left inverse for multiplication. -/
private theorem Implementation.group_left_inv {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    CartesianMonoidalCategory.lift (Bicategory.HomotopyCategory.mkHom (invHom f x)) (𝟙 (asHomotopy f x)) ≫ Bicategory.HomotopyCategory.mkHom (mulHom f x) =
      CartesianMonoidalCategory.toUnit (asHomotopy f x) ≫ Bicategory.HomotopyCategory.mkHom (oneHom f x) := sorry

/-- Inversion is a right inverse for multiplication. -/
private theorem Implementation.group_right_inv {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    CartesianMonoidalCategory.lift (𝟙 (asHomotopy f x)) (Bicategory.HomotopyCategory.mkHom (invHom f x)) ≫ Bicategory.HomotopyCategory.mkHom (mulHom f x) =
      CartesianMonoidalCategory.toUnit (asHomotopy f x) ≫ Bicategory.HomotopyCategory.mkHom (oneHom f x) := sorry

/-- Relative automorphisms form a group object over `Z`, with operations
pulled back from the identity, composition, and inversion of relative inertia. -/
instance instGrpObj_asHomotopy {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    GrpObj (asHomotopy f x) where
  one := Bicategory.HomotopyCategory.mkHom (oneHom f x)
  mul := Bicategory.HomotopyCategory.mkHom (mulHom f x)
  inv := Bicategory.HomotopyCategory.mkHom (invHom f x)
  one_mul := Implementation.group_one_mul f x
  mul_one := Implementation.group_mul_one f x
  mul_assoc := Implementation.group_mul_assoc f x
  left_inv := Implementation.group_left_inv f x
  right_inv := Implementation.group_right_inv f x

end GroupImplementation

end AlgebraicGeometry.AlgebraicStack.RelativeIsom
