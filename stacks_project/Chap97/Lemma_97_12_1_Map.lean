/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Equivalence
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Hom.Computations
public import stacks_project.Chap95.Lemma_95_18_1
public import stacks_project.Chap95.«95_18_2_1_Stack»

/-!
# Functoriality of finite Hilbert stacks along a 2-commutative square

A 2-commutative square of categories fibred in groupoids induces a 1-morphism
of finite Hilbert stacks by applying the fibre functors of the horizontal maps
and composing the comparison isomorphism with the given 2-cell.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}

/-- Applying the total functor of a groupoid-fibred morphism to a chosen cartesian
lift remains cartesian. -/
theorem fiberFunctorRestrict_isCartesian {X Y : GroupoidsOver S} (F : X ⟶ Y)
    {U Z : Over S} (x : X.p.Fiber U) (g : Z ⟶ U) :
    Y.p.IsCartesian g ((toFunctor F).map (IsPreFibered.pullbackMap x.property g)) :=
  sorry

/-- The fibre functor of `F` commutes with restriction along `g`, by uniqueness of
cartesian lifts. -/
def fiberFunctorRestrictIso {X Y : GroupoidsOver S} (F : X ⟶ Y)
    {U Z : Over S} (x : X.p.Fiber U) (g : Z ⟶ U) :
    (fiberFunctor F Z).obj (restrictObj x g) ≅
      restrictObj ((fiberFunctor F U).obj x) g :=
  let φ := IsPreFibered.pullbackMap ((fiberFunctor F U).obj x).property g
  let φ' := (toFunctor F).map (IsPreFibered.pullbackMap x.property g)
  let hφ := IsPreFibered.pullbackMap.IsCartesian ((fiberFunctor F U).obj x).property g
  let hφ' := fiberFunctorRestrict_isCartesian F x g
  Functor.Fiber.isoMk
    { hom := cartesianMap g φ hφ φ' hφ'.toIsHomLift
      inv := cartesianMap g φ' hφ' φ hφ.toIsHomLift
      hom_inv_id := sorry
      inv_hom_id := sorry }
    (cartesianMap_isHomLift g φ hφ φ' hφ'.toIsHomLift)

/-- The forward comparison of `fiberFunctorRestrictIso` inverts on the fibre over
`Z`. -/
theorem fiberFunctorRestrictIso_hom_inv_id {X Y : GroupoidsOver S} (F : X ⟶ Y)
    {U Z : Over S} (x : X.p.Fiber U) (g : Z ⟶ U) :
    (fiberFunctorRestrictIso F x g).hom ≫ (fiberFunctorRestrictIso F x g).inv =
      𝟙 ((fiberFunctor F Z).obj (restrictObj x g)) :=
  sorry

variable {X' X Y' Y : GroupoidsOver S}

/-- The comparison isomorphism `γ ⋆ H(α')` of the induced object, obtained by
restricting `H`, applying `H` to `α'`, identifying composite fibre functors, and
inserting the fibre of `γ`. -/
def mapSquareIso (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} (ξ : Obj F' d) :
    restrictObj ((fiberFunctor H ξ.U).obj ξ.y) ξ.π ≅
      (fiberFunctor F ξ.Z).obj ((fiberFunctor G ξ.Z).obj ξ.x) :=
  (fiberFunctorRestrictIso H ξ.y ξ.π).symm ≪≫
    (fiberFunctor H ξ.Z).mapIso ξ.iso ≪≫
    (eqToIso (congrArg (fun K ↦ K.obj ξ.x) (fiberFunctor.comp F' H ξ.Z))).symm ≪≫
    (BasedNatIso.fiber (toBasedFunctorIso γ) ξ.Z).app ξ.x ≪≫
    eqToIso (congrArg (fun K ↦ K.obj ξ.x) (fiberFunctor.comp G F ξ.Z))

/-- `mapSquareIso` is the displayed composite of restriction, `H(α')`, fibre-functor
composition, and the fibre of `γ`. -/
theorem mapSquareIso_eq (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} (ξ : Obj F' d) :
    mapSquareIso F' F G H γ ξ =
      (fiberFunctorRestrictIso H ξ.y ξ.π).symm ≪≫
        (fiberFunctor H ξ.Z).mapIso ξ.iso ≪≫
        (eqToIso (congrArg (fun K ↦ K.obj ξ.x) (fiberFunctor.comp F' H ξ.Z))).symm ≪≫
        (BasedNatIso.fiber (toBasedFunctorIso γ) ξ.Z).app ξ.x ≪≫
        eqToIso (congrArg (fun K ↦ K.obj ξ.x) (fiberFunctor.comp G F ξ.Z)) :=
  sorry

/-- Object part of the induced 1-morphism: copy `(U, Z, π)` and send
`(y, x, α)` to `(H(y), G(x), γ ⋆ H(α))`. -/
abbrev mapSquareObj (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} (ξ : Obj F' d) : Obj F d :=
  Obj.of ξ.U ξ.Z ξ.π ξ.finiteLocallyFree
    ((fiberFunctor H ξ.U).obj ξ.y) ((fiberFunctor G ξ.Z).obj ξ.x)
    (mapSquareIso F' F G H γ ξ)

/-- The `Y`-component of `mapSquareObj` is the fibre functor of `H` applied to `y`. -/
theorem mapSquareObj_y (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} (ξ : Obj F' d) :
    (mapSquareObj F' F G H γ ξ).y = (fiberFunctor H ξ.U).obj ξ.y :=
  sorry

/-- The `X`-component of `mapSquareObj` is the fibre functor of `G` applied to `x`. -/
theorem mapSquareObj_x (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} (ξ : Obj F' d) :
    (mapSquareObj F' F G H γ ξ).x = (fiberFunctor G ξ.Z).obj ξ.x :=
  sorry

/-- Morphism part of the induced 1-morphism: the same `(f, g)` with `b` and `a`
transported by the fibre functors of `H` and `G`. -/
def mapSquareHom (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} {ξ ξ' : Obj F' d} (φ : Hom ξ ξ') :
    Hom (mapSquareObj F' F G H γ ξ) (mapSquareObj F' F G H γ ξ') where
  f := φ.f
  g := φ.g
  over_comm := φ.over_comm
  isPullback := φ.isPullback
  b := (fiberFunctor H ξ.U).mapIso φ.b ≪≫ fiberFunctorRestrictIso H ξ'.y φ.f
  a := (fiberFunctor G ξ.Z).mapIso φ.a ≪≫ fiberFunctorRestrictIso G ξ'.x φ.g
  comm := sorry

/-- `mapSquareHom` preserves the underlying map of test schemes. -/
theorem mapSquareHom_f (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} {ξ ξ' : Obj F' d} (φ : Hom ξ ξ') :
    (mapSquareHom F' F G H γ φ).f = φ.f :=
  sorry

/-- `mapSquareHom` preserves the underlying map of finite locally free schemes. -/
theorem mapSquareHom_g (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} {ξ ξ' : Obj F' d} (φ : Hom ξ ξ') :
    (mapSquareHom F' F G H γ φ).g = φ.g :=
  sorry

/-- The `b`-component of `mapSquareHom` is the fibre functor of `H` applied to `b`. -/
theorem mapSquareHom_b (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} {ξ ξ' : Obj F' d} (φ : Hom ξ ξ') :
    (mapSquareHom F' F G H γ φ).b =
      (fiberFunctor H ξ.U).mapIso φ.b ≪≫ fiberFunctorRestrictIso H ξ'.y φ.f :=
  sorry

/-- The `a`-component of `mapSquareHom` is the fibre functor of `G` applied to `a`. -/
theorem mapSquareHom_a (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} {ξ ξ' : Obj F' d} (φ : Hom ξ ξ') :
    (mapSquareHom F' F G H γ φ).a =
      (fiberFunctor G ξ.Z).mapIso φ.a ≪≫ fiberFunctorRestrictIso G ξ'.x φ.g :=
  sorry

/-- The total functor of the induced 1-morphism `H_d(X'/Y') ⟶ H_d(X/Y)`. -/
def mapSquareFunctor (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    Obj F' d ⥤ Obj F d where
  obj ξ := mapSquareObj F' F G H γ ξ
  map φ := mapSquareHom F' F G H γ φ
  map_id := sorry
  map_comp := sorry

/-- `mapSquareFunctor` lies strictly over the identity on test schemes. -/
theorem mapSquareFunctor_w (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    mapSquareFunctor F' F G H γ d ⋙ p F d = p F' d :=
  sorry

/-- The image of a quintuple under `mapSquareFunctor` is `mapSquareObj`. -/
theorem mapSquare_obj (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) (ξ : Obj F' d) :
    (mapSquareFunctor F' F G H γ d).obj ξ = mapSquareObj F' F G H γ ξ :=
  sorry

/-- `mapSquareFunctor` preserves the underlying test scheme. -/
theorem mapSquare_U (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) (ξ : Obj F' d) :
    ((mapSquareFunctor F' F G H γ d).obj ξ).U = ξ.U :=
  sorry

/-- `mapSquareFunctor` preserves the finite locally free scheme. -/
theorem mapSquare_Z (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) (ξ : Obj F' d) :
    ((mapSquareFunctor F' F G H γ d).obj ξ).Z = ξ.Z :=
  sorry

/-- The `Y`-component of the image is `H(y)`. -/
theorem mapSquare_y (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) (ξ : Obj F' d) :
    ((mapSquareFunctor F' F G H γ d).obj ξ).y = (fiberFunctor H ξ.U).obj ξ.y :=
  sorry

/-- The `X`-component of the image is `G(x)`. -/
theorem mapSquare_x (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) (ξ : Obj F' d) :
    ((mapSquareFunctor F' F G H γ d).obj ξ).x = (fiberFunctor G ξ.Z).obj ξ.x :=
  sorry

/-- The comparison isomorphism of the image is `mapSquareIso`. -/
theorem mapSquare_iso (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) (ξ : Obj F' d) :
    ((mapSquareFunctor F' F G H γ d).obj ξ).iso = mapSquareIso F' F G H γ ξ :=
  sorry

/-- The based functor of the induced 1-morphism of finite Hilbert stacks. -/
def mapSquareBased (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    BasedCategory.ofFunctor (p F' d) ⥤ᵇ BasedCategory.ofFunctor (p F d) :=
  BasedFunctor.ofFunctor (mapSquareFunctor F' F G H γ d)
    (mapSquareFunctor_w F' F G H γ d)

/-- Forgetting `mapSquareBased` to total functors recovers `mapSquareFunctor`. -/
theorem mapSquareBased_toFunctor (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X)
    (H : Y' ⟶ Y) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    (mapSquareBased F' F G H γ d).toFunctor = mapSquareFunctor F' F G H γ d :=
  sorry

/-- A 1-morphism of groupoid fibrations over `S` is compatible with the canonical
projections to the identity fibration. -/
theorem schemeProjectionIso_isHomLift {X' X : GroupoidsOver S} (G : X' ⟶ X)
    (a : X'.total) :
    (schemeBase S).p.IsHomLift (𝟙 (X'.p.obj a))
      ((Functor.isoWhiskerRight (commIso G)
        (baseSection.{u + 1, u, u + 1} (Over S))).hom.app a) :=
  sorry

/-- The canonical 2-isomorphism `G ≫ (X ⟶ S) ≅ (X' ⟶ S)` of structure morphisms. -/
def schemeProjectionIso {X' X : GroupoidsOver S} (G : X' ⟶ X) :
    G ≫ baseProjection.{u + 1, u, u + 1} X ≅
      baseProjection.{u + 1, u, u + 1} X' :=
  BasedFunctorIso.lift
    (BasedNatIso.mkNatIso
      (Functor.isoWhiskerRight (commIso G)
        (baseSection.{u + 1, u, u + 1} (Over S)))
      (schemeProjectionIso_isHomLift G))

/-- `schemeProjectionIso` is the based-functor lift of whiskering `commIso` by the
canonical section. -/
theorem schemeProjectionIso_eq {X' X : GroupoidsOver S} (G : X' ⟶ X) :
    toBasedFunctorIso (schemeProjectionIso G) =
      BasedNatIso.mkNatIso
        (Functor.isoWhiskerRight (commIso G)
          (baseSection.{u + 1, u, u + 1} (Over S)))
        (schemeProjectionIso_isHomLift G) :=
  sorry

/-- The 2-cell `F' ≫ 𝟙 ≅ G ≫ F` of structure morphisms to `S`, in the orientation
required by `mapSquareIso`. -/
def schemeProjectionCell {X' X : GroupoidsOver S} (G : X' ⟶ X) :
    baseProjection.{u + 1, u, u + 1} X' ≫ 𝟙 (schemeBase S) ≅
      G ≫ baseProjection.{u + 1, u, u + 1} X :=
  (ρ_ (baseProjection.{u + 1, u, u + 1} X')).symm ≪≫ (schemeProjectionIso G).symm

/-- `schemeProjectionCell` is the inverse of `schemeProjectionIso` after the right
unitor. -/
theorem schemeProjectionCell_eq {X' X : GroupoidsOver S} (G : X' ⟶ X) :
    schemeProjectionCell G =
      (ρ_ (baseProjection.{u + 1, u, u + 1} X')).symm ≪≫
        (schemeProjectionIso G).symm :=
  sorry

variable {𝒳' 𝒳 𝒴' 𝒴 :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

open StackOver.Groupoids.Hom

/-- Transport a 2-isomorphism of stack morphisms to the underlying groupoid-fibred
square `F' ≫ H ≅ G ≫ F`. -/
def mapSquareCell (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴)
    (γ : F' ≫ H ≅ G ≫ F) :
    toGroupoidsMor F' ≫ toGroupoidsMor H ≅ toGroupoidsMor G ≫ toGroupoidsMor F :=
  eqToIso (toGroupoidsMor.comp F' H).symm ≪≫
    toGroupoidsMorIso γ ≪≫ eqToIso (toGroupoidsMor.comp G F)

/-- `mapSquareCell` is `toGroupoidsMorIso γ` after the composition identifications. -/
theorem mapSquareCell_eq (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴)
    (γ : F' ≫ H ≅ G ≫ F) :
    mapSquareCell F' F G H γ =
      eqToIso (toGroupoidsMor.comp F' H).symm ≪≫
        toGroupoidsMorIso γ ≪≫ eqToIso (toGroupoidsMor.comp G F) :=
  sorry

/-- The 1-morphism `H_d(𝒳'/𝒴') ⟶ H_d(𝒳/𝒴)` of stacks in groupoids induced by a
2-commutative square. -/
def mapSquare (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    stack (toGroupoidsMor F') d ⟶ stack (toGroupoidsMor F) d :=
  lift (ofBasedFunctor (mapSquareBased (toGroupoidsMor F') (toGroupoidsMor F)
    (toGroupoidsMor G) (toGroupoidsMor H) (mapSquareCell F' F G H γ) d))

/-- Forgetting `mapSquare` to based functors recovers `mapSquareBased` of the
underlying groupoid-fibred square. -/
theorem mapSquare_toBasedFunctor (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳)
    (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    toBasedFunctor (mapSquare F' F G H γ d) =
      mapSquareBased (toGroupoidsMor F') (toGroupoidsMor F) (toGroupoidsMor G)
        (toGroupoidsMor H) (mapSquareCell F' F G H γ) d :=
  sorry

/-- The 1-morphism `H_d(𝒳') ⟶ H_d(𝒳)` induced by `G` along structure morphisms to
`S`. -/
def mapSquareAbsolute (G : 𝒳' ⟶ 𝒳) (d : ℕ) :
    ofStack 𝒳'.toGroupoids d ⟶ ofStack 𝒳.toGroupoids d :=
  lift (ofBasedFunctor (mapSquareBased (toSchemeProjection 𝒳') (toSchemeProjection 𝒳)
    (toGroupoidsMor G) (𝟙 (schemeBase S)) (schemeProjectionCell (toGroupoidsMor G)) d))

/-- Forgetting `mapSquareAbsolute` to based functors recovers `mapSquareBased` of
the structure-morphism square. -/
theorem mapSquareAbsolute_toBasedFunctor (G : 𝒳' ⟶ 𝒳) (d : ℕ) :
    toBasedFunctor (mapSquareAbsolute G d) =
      mapSquareBased (toSchemeProjection 𝒳') (toSchemeProjection 𝒳)
        (toGroupoidsMor G) (𝟙 (schemeBase S))
        (schemeProjectionCell (toGroupoidsMor G)) d :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
