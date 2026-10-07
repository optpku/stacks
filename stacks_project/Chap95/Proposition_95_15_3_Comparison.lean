module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Precomposition
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
public import stacks_project.Chap78.Definition_78_20_1_Quotient
public import stacks_project.Chap95.Proposition_95_15_3_Quotient

/-!
# Canonical comparison of quotient stacks of a group action

This module constructs the 1-morphism `F_p : [X/_p G] ⟶ [[X/G]]` on the
prestack of the action groupoid and the selected stackification extension
`F : [X/G] ⟶ [[X/G]]`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupAlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace
open AlgebraicGeometry.QuotientStack.GroupAction
open CartesianMonoidalCategory MonoidalCategory
open Functor.IsFibered.InGroupoids.Stackification
open scoped CategoryTheory.MonObj MonoidalLeftAction
open scoped Bicategory
open scoped CategoryTheory.Pseudofunctor.CoGrothendieck

noncomputable section

universe u

namespace AlgebraicGeometry.QuotientStack.GroupAction

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- The morphism `b = π ∘ x : U ⟶ B` associated to a scheme-valued point of `X`. -/
def pointBase (G : GroupAlgebraicSpace B) (X : Action G) {U : Over S}
    (x : ofOver U ⟶ X.X.left) : ofOver U ⟶ B :=
  x ≫ X.X.hom

/-- `pointBase` is postcomposition with the structure morphism of `X`. -/
theorem pointBase_eq (G : GroupAlgebraicSpace B) (X : Action G) {U : Over S}
    (x : ofOver U ⟶ X.X.left) : pointBase G X x = x ≫ X.X.hom := sorry

/-- The unit of the slice over `U` has structure morphism the identity. -/
theorem pointSection_w (G : GroupAlgebraicSpace B) (X : Action G) {U : Over S}
    (x : ofOver U ⟶ X.X.left) :
    x ≫ X.X.hom = (𝟙_ (Over (ofOver U))).hom ≫ pointBase G X x := sorry

/-- The mediating map of `pointSection` lies over `U`. -/
theorem pointSection_hom_w (G : GroupAlgebraicSpace B) (X : Action G) {U : Over S}
    (x : ofOver U ⟶ X.X.left) :
    pullbackLift X.X.hom (pointBase G X x) x (𝟙_ (Over (ofOver U))).hom
        (pointSection_w G X x) ≫
      ((overPullback (pointBase G X x)).obj X.X).hom =
    (𝟙_ (Over (ofOver U))).hom := sorry

/-- The section of `X_U` associated to a scheme-valued point of `X`. -/
def pointSection (G : GroupAlgebraicSpace B) (X : Action G) {U : Over S}
    (x : ofOver U ⟶ X.X.left) :
    𝟙_ (Over (ofOver U)) ⟶ (overPullback (pointBase G X x)).obj X.X :=
  Over.homMk
    (pullbackLift X.X.hom (pointBase G X x) x (𝟙_ (Over (ofOver U))).hom
      (pointSection_w G X x))
    (pointSection_hom_w G X x)

/-- The map `a ∘ (id_G × x) : G_U ⟶ X_U` of the trivial torsor associated to `x`. -/
def trivialφ (G : GroupAlgebraicSpace B) (X : Action G) {U : Over S}
    (x : ofOver U ⟶ X.X.left) :
    (grpOverPullback G (pointBase G X x)).X ⟶
      (pullbackAction (pointBase G X x) G X).X :=
  (ρ_ ((grpOverPullback G (pointBase G X x)).X)).inv ≫
    ((grpOverPullback G (pointBase G X x)).X ◁ pointSection G X x) ≫
      (overPullbackμIso (pointBase G X x) G.X X.X).hom ≫
        (overPullback (pointBase G X x)).map γ[G.X, X.X]

/-- The left-regular `G_U`-action on itself. -/
def regularAction (G : GroupAlgebraicSpace B) {U : Over S} (b : ofOver U ⟶ B) :
    Action (grpOverPullback G b) where
  X := (grpOverPullback G b).X
  mod :=
    { smul := μ[(grpOverPullback G b).X]
      one_smul := sorry
      mul_smul := sorry }

/-- The underlying object of `regularAction` is `G_U`. -/
theorem regularAction_X (G : GroupAlgebraicSpace B) {U : Over S} (b : ofOver U ⟶ B) :
    (regularAction G b).X = (grpOverPullback G b).X := sorry

/-- The regular `G_U`-action is an fppf torsor. -/
theorem regular_isTorsor (G : GroupAlgebraicSpace B) (X : Action G) {U : Over S}
    (x : ofOver U ⟶ X.X.left) :
    IsStandardTorsor (grpOverPullback G (pointBase G X x))
      (regularAction G (pointBase G X x)) .fppf := sorry

/-- The map `trivialφ` is a morphism of `G_U`-actions. -/
theorem trivialφ_isEquivariant (G : GroupAlgebraicSpace B) (X : Action G) {U : Over S}
    (x : ofOver U ⟶ X.X.left) :
    IsEquivariantMap (regularAction G (pointBase G X x)) (trivialφ G X x) := sorry

/-- The object `F_p(U, x)` of `[[X/G]]`: the trivial `G_U`-torsor with equivariant
map `a ∘ (id_G × x)`. -/
def trivialObj (G : GroupAlgebraicSpace B) (X : Action G) {U : Over S}
    (x : ofOver U ⟶ X.X.left) : Obj G X :=
  ofTorsor U (pointBase G X x) (regularAction G (pointBase G X x))
    (regular_isTorsor G X x) (trivialφ G X x) (trivialφ_isEquivariant G X x)

/-- The underlying scheme of `trivialObj` is `U`. -/
theorem trivialObj_U (G : GroupAlgebraicSpace B) (X : Action G) {U : Over S}
    (x : ofOver U ⟶ X.X.left) : (trivialObj G X x).U = U := sorry

/-- A scheme-valued point of `G` over `U` is a section of `G_U`. -/
theorem sectionOf_w (G : GroupAlgebraicSpace B) {U : Over S} {b : ofOver U ⟶ B}
    (g : ofOver U ⟶ G.X.left) (hg : g ≫ G.X.hom = b) :
    g ≫ G.X.hom = (𝟙_ (Over (ofOver U))).hom ≫ b := sorry

/-- The mediating map of `sectionOf` lies over `U`. -/
theorem sectionOf_hom_w (G : GroupAlgebraicSpace B) {U : Over S} {b : ofOver U ⟶ B}
    (g : ofOver U ⟶ G.X.left) (hg : g ≫ G.X.hom = b) :
    pullbackLift G.X.hom b g (𝟙_ (Over (ofOver U))).hom (sectionOf_w G g hg) ≫
        (grpOverPullback G b).X.hom =
      (𝟙_ (Over (ofOver U))).hom := sorry

/-- The section of `G_U` associated to a scheme-valued point of `G` over `b`. -/
def sectionOf (G : GroupAlgebraicSpace B) {U : Over S} {b : ofOver U ⟶ B}
    (g : ofOver U ⟶ G.X.left) (hg : g ≫ G.X.hom = b) :
    𝟙_ (Over (ofOver U)) ⟶ (grpOverPullback G b).X :=
  Over.homMk
    (pullbackLift G.X.hom b g (𝟙_ (Over (ofOver U))).hom (sectionOf_w G g hg))
    (sectionOf_hom_w G g hg)

/-- Right multiplication by a section of `G_U`. -/
def rightMul (G : GroupAlgebraicSpace B) {U : Over S} {b : ofOver U ⟶ B}
    (g : ofOver U ⟶ G.X.left) (hg : g ≫ G.X.hom = b) :
    (grpOverPullback G b).X ⟶ (grpOverPullback G b).X :=
  (ρ_ ((grpOverPullback G b).X)).inv ≫
    ((grpOverPullback G b).X ◁ sectionOf G g hg) ≫ μ[(grpOverPullback G b).X]

/-- The inverse section of `G_U` still lies over `b`. -/
theorem inv_section_w (G : GroupAlgebraicSpace B) {U : Over S} {b : ofOver U ⟶ B}
    (g : ofOver U ⟶ G.X.left) (hg : g ≫ G.X.hom = b) :
    (g ≫ ι[G.X].left) ≫ G.X.hom = b := sorry

/-- Right multiplication by a section of `G_U` is an isomorphism. -/
def rightMulIso (G : GroupAlgebraicSpace B) {U : Over S} {b : ofOver U ⟶ B}
    (g : ofOver U ⟶ G.X.left) (hg : g ≫ G.X.hom = b) :
    (grpOverPullback G b).X ≅ (grpOverPullback G b).X where
  hom := rightMul G g hg
  inv := rightMul G (g ≫ ι[G.X].left) (inv_section_w G g hg)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Right translation `R_{g⁻¹}` as an isomorphism of trivial `G_U`-torsors after
pullback along `f`. -/
def rightTranslation (G : GroupAlgebraicSpace B) (X : Action G) {U U' : Over S}
    (x : ofOver U ⟶ X.X.left) (x' : ofOver U' ⟶ X.X.left) (f : U ⟶ U')
    (g : ofOver U ⟶ G.X.left)
    (hb : pointBase G X x = ofOverMap f ≫ pointBase G X x')
    (hg : g ≫ G.X.hom = pointBase G X x) :
    (trivialObj G X x).P.X ≅
      (overPullback (ofOverMap f)).obj (trivialObj G X x').P.X :=
  (rightMulIso G g hg).symm ≪≫
    eqToIso (congrArg (fun t ↦ (overPullback t).obj G.X) hb) ≪≫
      overPullbackCompIso (pointBase G X x') (ofOverMap f) G.X

/-- The co-Grothendieck total category of `[X/_p G]`. -/
abbrev actionPrestackTotal (G : GroupAlgebraicSpace B) (X : Action G) :=
  (preQuotient (ofAction G X)).total

/-- The scheme-valued point of `X` carried by an object of `[X/_p G]`. -/
def prestackPoint (G : GroupAlgebraicSpace B) (X : Action G)
    (ξ : actionPrestackTotal G X) : ofOver ξ.base ⟶ X.X.left :=
  ξ.fiber

/-- The `G`-component of a morphism of the action groupoid of scheme-valued points. -/
def preHomGroup (G : GroupAlgebraicSpace B) (X : Action G)
    {ξ ξ' : actionPrestackTotal G X} (p : ξ ⟶ ξ') :
    ofOver ξ.base ⟶ G.X.left :=
  p.fiber.arrow ≫ (fst G.X X.X).left

/-- Compatibility of `preHomGroup` with the structure morphism of `G`. -/
theorem preHomGroup_w (G : GroupAlgebraicSpace B) (X : Action G)
    {ξ ξ' : actionPrestackTotal G X} (p : ξ ⟶ ξ') :
    preHomGroup G X p ≫ G.X.hom = pointBase G X (prestackPoint G X ξ) := sorry

/-- A morphism of `[X/_p G]` lies over `B` on the associated points of `X`. -/
theorem preHom_comm (G : GroupAlgebraicSpace B) (X : Action G)
    {ξ ξ' : actionPrestackTotal G X} (p : ξ ⟶ ξ') :
    pointBase G X (prestackPoint G X ξ) = ofOverMap p.base ≫ pointBase G X (prestackPoint G X ξ') := sorry

/-- Right translation `R_{g⁻¹}` associated to a morphism of `[X/_p G]`. -/
def preHomIso (G : GroupAlgebraicSpace B) (X : Action G)
    {ξ ξ' : actionPrestackTotal G X} (p : ξ ⟶ ξ') :
    (trivialObj G X (prestackPoint G X ξ)).P.X ≅
      (overPullback (ofOverMap p.base)).obj
        (trivialObj G X (prestackPoint G X ξ')).P.X :=
  rightTranslation G X (prestackPoint G X ξ) (prestackPoint G X ξ') p.base
    (preHomGroup G X p) (preHom_comm G X p) (preHomGroup_w G X p)

/-- The action of `F_p` on morphisms of `[X/_p G]`. -/
def preHomFunctorMap (G : GroupAlgebraicSpace B) (X : Action G)
    {ξ ξ' : actionPrestackTotal G X} (p : ξ ⟶ ξ') :
    Hom (trivialObj G X (prestackPoint G X ξ)) (trivialObj G X (prestackPoint G X ξ')) where
  f := p.base
  comm := preHom_comm G X p
  g := preHomIso G X p
  equivariant := sorry
  triangle := sorry

/-- `F_p` preserves identity morphisms. -/
theorem preHomFunctor_map_id (G : GroupAlgebraicSpace B) (X : Action G)
    (ξ : actionPrestackTotal G X) :
    preHomFunctorMap G X (𝟙 ξ) = idHom (trivialObj G X (prestackPoint G X ξ)) := sorry

/-- `F_p` preserves composition. -/
theorem preHomFunctor_map_comp (G : GroupAlgebraicSpace B) (X : Action G)
    {ξ ξ' ξ'' : actionPrestackTotal G X} (p : ξ ⟶ ξ') (q : ξ' ⟶ ξ'') :
    preHomFunctorMap G X (p ≫ q) =
      compHom (preHomFunctorMap G X p) (preHomFunctorMap G X q) := sorry

/-- The functor `F_p : [X/_p G] ⟶ [[X/G]]` on total categories. -/
def preHomFunctor (G : GroupAlgebraicSpace B) (X : Action G) :
    (preQuotient (ofAction G X)).total ⥤ Obj G X where
  obj ξ := trivialObj G X (prestackPoint G X ξ)
  map p := preHomFunctorMap G X p
  map_id := preHomFunctor_map_id G X
  map_comp := preHomFunctor_map_comp G X

/-- `preHomFunctor` sends a prestack point `(U, x)` to `trivialObj x`. -/
theorem preHomFunctor_obj (G : GroupAlgebraicSpace B) (X : Action G)
    (ξ : actionPrestackTotal G X) :
    (preHomFunctor G X).obj ξ = trivialObj G X (prestackPoint G X ξ) := sorry

/-- The functor `F_p` lies over `(Sch/S)_fppf`. -/
theorem preHomFunctor_w (G : GroupAlgebraicSpace B) (X : Action G) :
    preHomFunctor G X ⋙ forget G X = (preQuotient (ofAction G X)).p := sorry

/-- The cartesian 1-morphism `F_p : [X/_p G] ⟶ [[X/G]]` over `(Sch/S)_fppf`. -/
def preHom (G : GroupAlgebraicSpace B) (X : Action G) :=
  cartesianOver (preQuotient (ofAction G X)).p (preHomFunctor G X)
    (preHomFunctor_w G X)

/-- The selected stackification lift of `F_p` through `[X/_p G] ⟶ [X/G]`. -/
def homLift (G : GroupAlgebraicSpace B) (X : Action G) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (stackificationPresentation (ofAction G X)).isStackification (preHom G X)

/-- The canonical 1-morphism `[X/G] ⟶ [[X/G]]` of stacks in groupoids over
`(Sch/S)_fppf`. -/
def equivalent (G : GroupAlgebraicSpace B) (X : Action G) :=
  (homLift G X).lift

/-- Precomposing `equivalent` with stackification of `[X/_p G]` recovers `F_p`. -/
def preHom_comp (G : GroupAlgebraicSpace B) (X : Action G) :
    (CartesianBasedFunctor.precomp (forget G X)
        (stackificationPresentation (ofAction G X)).comparison).obj
      (equivalent G X) ≅ preHom G X :=
  (homLift G X).comparison

/-- The comparison `[X/G] ⟶ [[X/G]]` is an equivalence of categories over
`(Sch/S)_fppf`. -/
instance equivalent_isEquivalence (G : GroupAlgebraicSpace B) (X : Action G) :
    (equivalent G X).toBasedFunctor.IsEquivalence := sorry

end AlgebraicGeometry.QuotientStack.GroupAction
