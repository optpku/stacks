module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Core
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import stacks_project.Chap98.Lemma_98_21_1_Lift

/-!
# Action of groupoid-fibred 1-morphisms on lift categories

A 1-morphism `F : X ⟶ Y` of categories fibred in groupoids, together with a commutative
square in the base and a fibre morphism `φ : F(x)|_r ⟶ y`, induces a functor of
fibered lift categories `UnderLift X.p i x ⥤ UnderLift Y.p j y`.
-/

@[expose] public section

universe u v w vS

open CategoryTheory
open scoped Bicategory

noncomputable section

namespace CategoryTheory.FiberedCategoryOver.Groupoids

open Functor
open Fiber

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids C}

/-- The total morphism `y ⟶ F(x)` over `r` associated to a fibre morphism
`φ : F(x)|_r ⟶ y`. -/
def ofHomLift (F : X ⟶ Y) {U V : C} (r : V ⟶ U) {x : X.p.Fiber U} {y : Y.p.Fiber V}
    (φ : Chosen.reindexObj Y.p r ((fiberFunctor F U).obj x) ⟶ y) :
    y.1 ⟶ ((fiberFunctor F U).obj x).1 :=
  Fiber.fiberInclusion.map (inv φ) ≫
    Chosen.cartesianHom Y.p r ((fiberFunctor F U).obj x)

/-- `ofHomLift F r φ` lies over the base arrow `r`. -/
instance ofHomLift.isHomLift (F : X ⟶ Y) {U V : C} (r : V ⟶ U)
    {x : X.p.Fiber U} {y : Y.p.Fiber V}
    (φ : Chosen.reindexObj Y.p r ((fiberFunctor F U).obj x) ⟶ y) :
    Y.p.IsHomLift r (ofHomLift F r φ) := sorry

/-- Recover a fibre morphism `F(x)|_r ⟶ y` from a total morphism `y ⟶ F(x)` over `r`. -/
def fiberHomOfHomLift (F : X ⟶ Y) {U V : C} (r : V ⟶ U)
    {x : X.p.Fiber U} {y : Y.p.Fiber V}
    (ψ : y.1 ⟶ ((fiberFunctor F U).obj x).1) [Y.p.IsHomLift r ψ] :
    Chosen.reindexObj Y.p r ((fiberFunctor F U).obj x) ⟶ y :=
  inv ⟨Chosen.cartesianFactor Y.p r (𝟙 V) ((fiberFunctor F U).obj x) ψ, inferInstance⟩

/-- `fiberHomOfHomLift` inverts `ofHomLift` on fibre morphisms. -/
theorem fiberHomOfHomLift_ofHomLift (F : X ⟶ Y) {U V : C} (r : V ⟶ U)
    {x : X.p.Fiber U} {y : Y.p.Fiber V}
    (φ : Chosen.reindexObj Y.p r ((fiberFunctor F U).obj x) ⟶ y) :
    fiberHomOfHomLift F r (ofHomLift F r φ) = φ := sorry

/-- `Chosen.cartesianFactor` with an explicit hom-lift certificate. -/
def cartesianFactorOf {𝒳 : Type w} [Category.{vS} 𝒳]
    (p : 𝒳 ⥤ C) [p.IsFibered] {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (x : p.Fiber U) {a : 𝒳} (φ : a ⟶ x.1) (h : p.IsHomLift (g ≫ f) φ) :
    a ⟶ (Chosen.reindexObj p f x).1 :=
  @Chosen.cartesianFactor C _ 𝒳 _ p _ U V W f g x a φ h

/-- The explicit cartesian factor lies over the remaining base arrow. -/
instance cartesianFactorOf_isHomLift {𝒳 : Type w} [Category.{vS} 𝒳]
    (p : 𝒳 ⥤ C) [p.IsFibered] {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (x : p.Fiber U) {a : 𝒳} (φ : a ⟶ x.1) (h : p.IsHomLift (g ≫ f) φ) :
    p.IsHomLift g (cartesianFactorOf p f g x φ h) := sorry

/-- Applying a based 1-morphism to a selected cartesian arrow still lifts `𝟙 V ≫ r`. -/
theorem map_cartesianHom_id_comp_isHomLift {Z : FiberedCategoryOver.Groupoids C}
    (G : Y ⟶ Z) {U V : C} (r : V ⟶ U) (y : Y.p.Fiber U) :
    Z.p.IsHomLift (𝟙 V ≫ r)
      ((toBasedFunctor G).map (Chosen.cartesianHom Y.p r y)) := sorry

/-- A selected cartesian arrow still lifts `𝟙 V ≫ r`. -/
theorem cartesianHom_id_comp_isHomLift {Z : FiberedCategoryOver.Groupoids C}
    {U V : C} (r : V ⟶ U) (z : Z.p.Fiber U) :
    Z.p.IsHomLift (𝟙 V ≫ r) (Chosen.cartesianHom Z.p r z) := sorry

/-- Comparison `G(y|_r) ⟶ G(y)|_r` obtained by cartesian factorization of
`G` applied to the selected cartesian arrow of `y`. -/
def reindexCompare {Z : FiberedCategoryOver.Groupoids C} (G : Y ⟶ Z)
    {U V : C} (r : V ⟶ U) (y : Y.p.Fiber U) :
    (fiberFunctor G V).obj (Chosen.reindexObj Y.p r y) ⟶
      Chosen.reindexObj Z.p r ((fiberFunctor G U).obj y) :=
  ⟨cartesianFactorOf Z.p r (𝟙 V) ((fiberFunctor G U).obj y)
      ((toBasedFunctor G).map (Chosen.cartesianHom Y.p r y))
      (map_cartesianHom_id_comp_isHomLift G r y),
    inferInstance⟩

/-- Comparison `(G ∘ F)(x)|_r ⟶ G(F(x))|_r` obtained by cartesian factorization through
the selected cartesian arrow of `G(F(x))`. -/
def reindexCompCompare {Z : FiberedCategoryOver.Groupoids C} (F : X ⟶ Y) (G : Y ⟶ Z)
    {U V : C} (r : V ⟶ U) (x : X.p.Fiber U) :
    Chosen.reindexObj Z.p r ((fiberFunctor (F ≫ G) U).obj x) ⟶
      Chosen.reindexObj Z.p r ((fiberFunctor G U).obj ((fiberFunctor F U).obj x)) :=
  ⟨cartesianFactorOf Z.p r (𝟙 V)
      ((fiberFunctor G U).obj ((fiberFunctor F U).obj x))
      (Chosen.cartesianHom Z.p r ((fiberFunctor (F ≫ G) U).obj x))
      (cartesianHom_id_comp_isHomLift r ((fiberFunctor (F ≫ G) U).obj x)),
    inferInstance⟩

/-- The composite total morphism `y ⟶ F(x')` over `j ≫ r'` associated to a lift of `x`. -/
def connectHom (F : X ⟶ Y) {U U' V V' : C}
    (i : U ⟶ U') (j : V ⟶ V') (r : V ⟶ U) (r' : V' ⟶ U') (_ : CommSq j r r' i)
    {x : X.p.Fiber U} {y : Y.p.Fiber V}
    (φ : Chosen.reindexObj Y.p r ((fiberFunctor F U).obj x) ⟶ y)
    (a : UnderLift X.p i x) :
    y.1 ⟶ (toFunctor F).obj a.right :=
  ofHomLift F r φ ≫ (toBasedFunctor F).map a.hom

/-- `connectHom` lies over `j ≫ r'`. -/
instance connectHom_isHomLift (F : X ⟶ Y) {U U' V V' : C}
    (i : U ⟶ U') (j : V ⟶ V') (r : V ⟶ U) (r' : V' ⟶ U') (sq : CommSq j r r' i)
    {x : X.p.Fiber U} {y : Y.p.Fiber V}
    (φ : Chosen.reindexObj Y.p r ((fiberFunctor F U).obj x) ⟶ y)
    (a : UnderLift X.p i x) :
    Y.p.IsHomLift (j ≫ r') (connectHom F i j r r' sq φ a) := sorry

/-- A 1-morphism of categories fibred in groupoids, together with a commutative square
in the base and a fibre morphism `φ : F(x)|_r ⟶ y`, induces a functor of lift
categories. -/
def liftFunctor (F : X ⟶ Y) {U U' V V' : C}
    (i : U ⟶ U') (j : V ⟶ V') (r : V ⟶ U) (r' : V' ⟶ U') (sq : CommSq j r r' i)
    {x : X.p.Fiber U} {y : Y.p.Fiber V}
    (φ : Chosen.reindexObj Y.p r ((fiberFunctor F U).obj x) ⟶ y) :
    UnderLift X.p i x ⥤ UnderLift Y.p j y where
  obj a :=
    UnderLift.ofHom j y
      (cartesianFactorOf Y.p r' j ((fiberFunctor F U').obj a.codomain)
        (connectHom F i j r r' sq φ a)
        (connectHom_isHomLift F i j r r' sq φ a))
  map {a b} η :=
    let ψ := Chosen.reindexMap Y.p r' ((fiberFunctor F U').map η.val)
    UnderLift.homMk ⟨ψ.val, ψ.property⟩ sorry
  map_id := sorry
  map_comp := sorry

/-- The image of a lift under `liftFunctor` lies over `j`. -/
theorem liftFunctor_obj (F : X ⟶ Y) {U U' V V' : C}
    (i : U ⟶ U') (j : V ⟶ V') (r : V ⟶ U) (r' : V' ⟶ U') (sq : CommSq j r r' i)
    {x : X.p.Fiber U} {y : Y.p.Fiber V}
    (φ : Chosen.reindexObj Y.p r ((fiberFunctor F U).obj x) ⟶ y)
    (a : UnderLift X.p i x) :
    Y.p.IsHomLift j ((liftFunctor F i j r r' sq φ).obj a).hom := sorry

/-- A morphism of lifts is sent to a fibre morphism over the codomain of `j`. -/
theorem liftFunctor_map (F : X ⟶ Y) {U U' V V' : C}
    (i : U ⟶ U') (j : V ⟶ V') (r : V ⟶ U) (r' : V' ⟶ U') (sq : CommSq j r r' i)
    {x : X.p.Fiber U} {y : Y.p.Fiber V}
    (φ : Chosen.reindexObj Y.p r ((fiberFunctor F U).obj x) ⟶ y)
    {a b : UnderLift X.p i x} (η : a ⟶ b) :
    Y.p.IsHomLift (𝟙 V')
      (Fiber.fiberInclusion.map ((liftFunctor F i j r r' sq φ).map η).val) := sorry

namespace liftFunctor

/-- The composite connecting fibre morphism for `G ∘ F`, sending `(G ∘ F)(x)|_r` to `G(y)`. -/
def connect {Z : FiberedCategoryOver.Groupoids C} (F : X ⟶ Y) (G : Y ⟶ Z)
    {U V : C} (r : V ⟶ U) {x : X.p.Fiber U} {y : Y.p.Fiber V}
    (φ : Chosen.reindexObj Y.p r ((fiberFunctor F U).obj x) ⟶ y) :
    Chosen.reindexObj Z.p r ((fiberFunctor (F ≫ G) U).obj x) ⟶
      (fiberFunctor G V).obj y :=
  reindexCompCompare F G r x ≫
    inv (reindexCompare G r ((fiberFunctor F U).obj x)) ≫
    (fiberFunctor G V).map φ

/-- The canonical fibre morphism `G(y)|_{𝟙 V} ⟶ G(y)` used when applying `G` on the same
base object. -/
def idConnect {Z : FiberedCategoryOver.Groupoids C} (G : Y ⟶ Z)
    {V : C} (y : Y.p.Fiber V) :
    Chosen.reindexObj Z.p (𝟙 V) ((fiberFunctor G V).obj y) ⟶ (fiberFunctor G V).obj y :=
  ⟨Chosen.cartesianHom Z.p (𝟙 V) ((fiberFunctor G V).obj y),
    Chosen.cartesianHom.isHomLift Z.p (𝟙 V) ((fiberFunctor G V).obj y)⟩

/-- Applying `G` to lifts of `y` along `j`, using the identity connecting morphism on `G(y)`. -/
def onId {Z : FiberedCategoryOver.Groupoids C} (G : Y ⟶ Z)
    {V V' : C} (j : V ⟶ V') (y : Y.p.Fiber V) :
    UnderLift Y.p j y ⥤ UnderLift Z.p j ((fiberFunctor G V).obj y) :=
  liftFunctor G j j (𝟙 V) (𝟙 V') ⟨sorry⟩ (idConnect G y)

/-- The identity-cleavage comparison from a lift of `x` along `i` to its selected restriction
along `𝟙 U'`. -/
def idFibre (X : FiberedCategoryOver.Groupoids C) {U U' : C} (i : U ⟶ U')
    (x : X.p.Fiber U) (a : UnderLift X.p i x) :
    a.codomain ⟶
      ((liftFunctor (𝟙 X) i i (𝟙 U) (𝟙 U') ⟨sorry⟩ (idConnect (𝟙 X) x)).obj a).codomain :=
  ⟨(Cleavage.Reindex.idAmbientIso (Cleavage.ofIsFibered X.p) U' a.codomain).hom, sorry⟩

/-- The identity-cleavage comparison inverts `idFibre`. -/
def idFibreInv (X : FiberedCategoryOver.Groupoids C) {U U' : C} (i : U ⟶ U')
    (x : X.p.Fiber U) (a : UnderLift X.p i x) :
    ((liftFunctor (𝟙 X) i i (𝟙 U) (𝟙 U') ⟨sorry⟩ (idConnect (𝟙 X) x)).obj a).codomain ⟶
      a.codomain :=
  ⟨(Cleavage.Reindex.idAmbientIso (Cleavage.ofIsFibered X.p) U' a.codomain).inv, sorry⟩

/-- Fibre comparison from the direct `r'`-restriction of `(G ∘ F)(x')` to the identity
restriction used by `onId`. -/
def compFibre {Z : FiberedCategoryOver.Groupoids C} (F : X ⟶ Y) (G : Y ⟶ Z)
    {U U' V V' : C} (i : U ⟶ U') (j : V ⟶ V') (r : V ⟶ U) (r' : V' ⟶ U')
    (sq : CommSq j r r' i) {x : X.p.Fiber U} {y : Y.p.Fiber V}
    (φ : Chosen.reindexObj Y.p r ((fiberFunctor F U).obj x) ⟶ y)
    (a : UnderLift X.p i x) :
    ((liftFunctor (F ≫ G) i j r r' sq (connect F G r φ)).obj a).codomain ⟶
      ((liftFunctor F i j r r' sq φ ⋙ onId G j y).obj a).codomain :=
  ⟨(reindexCompCompare F G r' a.codomain).1 ≫
      (inv (reindexCompare G r' ((fiberFunctor F U').obj a.codomain))).1 ≫
      (Cleavage.Reindex.idIsoApp (Cleavage.ofIsFibered Z.p) V'
        ((fiberFunctor G V').obj ((liftFunctor F i j r r' sq φ).obj a).codomain)).hom.1,
    sorry⟩

/-- Inverse fibre comparison for `compFibre`, using the inverse identity-cleavage component. -/
def compFibreInv {Z : FiberedCategoryOver.Groupoids C} (F : X ⟶ Y) (G : Y ⟶ Z)
    {U U' V V' : C} (i : U ⟶ U') (j : V ⟶ V') (r : V ⟶ U) (r' : V' ⟶ U')
    (sq : CommSq j r r' i) {x : X.p.Fiber U} {y : Y.p.Fiber V}
    (φ : Chosen.reindexObj Y.p r ((fiberFunctor F U).obj x) ⟶ y)
    (a : UnderLift X.p i x) :
    ((liftFunctor F i j r r' sq φ ⋙ onId G j y).obj a).codomain ⟶
      ((liftFunctor (F ≫ G) i j r r' sq (connect F G r φ)).obj a).codomain :=
  ⟨(Cleavage.Reindex.idIsoApp (Cleavage.ofIsFibered Z.p) V'
        ((fiberFunctor G V').obj ((liftFunctor F i j r r' sq φ).obj a).codomain)).inv.1 ≫
      (reindexCompare G r' ((fiberFunctor F U').obj a.codomain)).1 ≫
      (inv (reindexCompCompare F G r' a.codomain)).1,
    sorry⟩

end liftFunctor

/-- `idFibre` is the selected identity-cleavage comparison on the fibre over the codomain. -/
theorem liftFunctor.idFibre_spec (X : FiberedCategoryOver.Groupoids C)
    {U U' : C} (i : U ⟶ U') (x : X.p.Fiber U) (a : UnderLift X.p i x) :
    (liftFunctor.idFibre X i x a).1 =
      (Cleavage.Reindex.idAmbientIso (Cleavage.ofIsFibered X.p) U' a.codomain).hom := sorry

/-- `compFibre` is the composite of reindexing comparisons with the identity-cleavage component. -/
theorem liftFunctor.compFibre_spec {Z : FiberedCategoryOver.Groupoids C}
    (F : X ⟶ Y) (G : Y ⟶ Z) {U U' V V' : C}
    (i : U ⟶ U') (j : V ⟶ V') (r : V ⟶ U) (r' : V' ⟶ U') (sq : CommSq j r r' i)
    {x : X.p.Fiber U} {y : Y.p.Fiber V}
    (φ : Chosen.reindexObj Y.p r ((fiberFunctor F U).obj x) ⟶ y)
    (a : UnderLift X.p i x) :
    (liftFunctor.compFibre F G i j r r' sq φ a).1 =
      (reindexCompCompare F G r' a.codomain).1 ≫
        (inv (reindexCompare G r' ((fiberFunctor F U').obj a.codomain))).1 ≫
        (Cleavage.Reindex.idIsoApp (Cleavage.ofIsFibered Z.p) V'
          ((fiberFunctor G V').obj ((liftFunctor F i j r r' sq φ).obj a).codomain)).hom.1 := sorry

/-- `idFibreInv` is the inverse selected identity-cleavage comparison. -/
theorem liftFunctor.idFibreInv_spec (X : FiberedCategoryOver.Groupoids C)
    {U U' : C} (i : U ⟶ U') (x : X.p.Fiber U) (a : UnderLift X.p i x) :
    (liftFunctor.idFibreInv X i x a).1 =
      (Cleavage.Reindex.idAmbientIso (Cleavage.ofIsFibered X.p) U' a.codomain).inv := sorry

/-- `compFibreInv` reverses `compFibre` along the selected identity-cleavage comparison. -/
theorem liftFunctor.compFibreInv_spec {Z : FiberedCategoryOver.Groupoids C}
    (F : X ⟶ Y) (G : Y ⟶ Z) {U U' V V' : C}
    (i : U ⟶ U') (j : V ⟶ V') (r : V ⟶ U) (r' : V' ⟶ U') (sq : CommSq j r r' i)
    {x : X.p.Fiber U} {y : Y.p.Fiber V}
    (φ : Chosen.reindexObj Y.p r ((fiberFunctor F U).obj x) ⟶ y)
    (a : UnderLift X.p i x) :
    (liftFunctor.compFibreInv F G i j r r' sq φ a).1 =
      (Cleavage.Reindex.idIsoApp (Cleavage.ofIsFibered Z.p) V'
          ((fiberFunctor G V').obj ((liftFunctor F i j r r' sq φ).obj a).codomain)).inv.1 ≫
        (reindexCompare G r' ((fiberFunctor F U').obj a.codomain)).1 ≫
        (inv (reindexCompCompare F G r' a.codomain)).1 := sorry

/-- The identity 1-morphism acts as the identity on lift categories, up to the selected
identity cartesian arrow. -/
def liftFunctor_id (X : FiberedCategoryOver.Groupoids C) {U U' : C} (i : U ⟶ U')
    (x : X.p.Fiber U) :
    liftFunctor (𝟙 X) i i (𝟙 U) (𝟙 U') ⟨sorry⟩ (liftFunctor.idConnect (𝟙 X) x) ≅
      𝟭 (UnderLift X.p i x) :=
  NatIso.ofComponents
    (fun a ↦
      { hom := UnderLift.homMk (liftFunctor.idFibreInv X i x a) sorry
        inv := UnderLift.homMk (liftFunctor.idFibre X i x a) sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (fun _ ↦ sorry)

/-- The forward component of `liftFunctor_id` is the inverse identity-cleavage comparison. -/
theorem liftFunctor_id_hom_app (X : FiberedCategoryOver.Groupoids C)
    {U U' : C} (i : U ⟶ U') (x : X.p.Fiber U) (a : UnderLift X.p i x) :
    ((liftFunctor_id X i x).hom.app a).val = liftFunctor.idFibreInv X i x a := sorry

/-- Composition of 1-morphisms is compatible with the induced functors of lift categories. -/
def liftFunctor_comp {Z : FiberedCategoryOver.Groupoids C} (F : X ⟶ Y) (G : Y ⟶ Z)
    {U U' V V' : C} (i : U ⟶ U') (j : V ⟶ V') (r : V ⟶ U) (r' : V' ⟶ U')
    (sq : CommSq j r r' i) {x : X.p.Fiber U} {y : Y.p.Fiber V}
    (φ : Chosen.reindexObj Y.p r ((fiberFunctor F U).obj x) ⟶ y) :
    liftFunctor (F ≫ G) i j r r' sq (liftFunctor.connect F G r φ) ≅
      liftFunctor F i j r r' sq φ ⋙ liftFunctor.onId G j y :=
  NatIso.ofComponents
    (fun a ↦
      { hom := UnderLift.homMk (liftFunctor.compFibre F G i j r r' sq φ a) sorry
        inv := UnderLift.homMk (liftFunctor.compFibreInv F G i j r r' sq φ a) sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (fun _ ↦ sorry)

/-- The forward component of `liftFunctor_comp` is the selected cleavage comparison. -/
theorem liftFunctor_comp_hom_app {Z : FiberedCategoryOver.Groupoids C}
    (F : X ⟶ Y) (G : Y ⟶ Z) {U U' V V' : C}
    (i : U ⟶ U') (j : V ⟶ V') (r : V ⟶ U) (r' : V' ⟶ U') (sq : CommSq j r r' i)
    {x : X.p.Fiber U} {y : Y.p.Fiber V}
    (φ : Chosen.reindexObj Y.p r ((fiberFunctor F U).obj x) ⟶ y)
    (a : UnderLift X.p i x) :
    ((liftFunctor_comp F G i j r r' sq φ).hom.app a).val =
      liftFunctor.compFibre F G i j r r' sq φ a := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids
