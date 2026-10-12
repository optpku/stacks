/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap78.Definition_78_19_1_QuotientSheaf
public import stacks_project.Chap97.«97_10_0_2_Presheaf»
public import stacks_project.Chap97.Lemma_97_10_1_SpacePair

/-!
# The relative-Hom fppf sheaf

The functor `Mor_B(Z, X)` is an fppf sheaf on `Sch/S`, and morphisms of sheaves
out of an algebraic space `T` correspond to 05Y1 pairs over `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

/-- The relative-Hom functor `Mor_B(Z, X)` is a sheaf for the fppf topology on
schemes over `S`. -/
theorem functor_isSheaf {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (functor Z X) :=
  sorry

/-- The relative-Hom sheaf `Mor_B(Z, X)` on `(Sch/S)_fppf`. -/
def homSheaf {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨functor Z X, functor_isSheaf Z X⟩

/-- Evaluating `homSheaf Z X` at a scheme `T` over `S` recovers the type of
scheme-level pairs. -/
theorem homSheaf_obj {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    (T : Over S) : (homSheaf Z X).obj.obj (op T) = HomPair Z X T :=
  sorry

/-- The underlying presheaf morphism of `toBase`, sending a pair `(a, b)` to the
universe-lift of the Yoneda equivalent of `a`. -/
def toBase_hom {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) :
    (homSheaf Z X).obj ⟶ (uliftSheaf B).obj where
  app T := TypeCat.ofHom fun p ↦ ULift.up (yonedaEquiv p.base)
  naturality := sorry

/-- The structure morphism `Mor_B(Z, X) ⟶ B` of fppf sheaves. -/
def toBase {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) :
    homSheaf Z X ⟶ uliftSheaf B :=
  Sheaf.homEquiv.symm (toBase_hom Z X)

/-- The underlying presheaf morphism of `toBase` is `toBase_hom`. -/
theorem toBase_hom_eq {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) :
    (toBase Z X).hom = toBase_hom Z X :=
  sorry

/-- The component of `toBase` at `T` sends a pair to the universe-lift of the
Yoneda equivalent of its base morphism. -/
theorem toBase_app {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    (T : (Over S)ᵒᵖ) (p : HomPair Z X T.unop) :
    (toBase Z X).hom.app T p = ULift.up (yonedaEquiv p.base) :=
  sorry

/-- The presheaf morphism associated to a pair over an algebraic space, sending a
scheme-valued point of `T` to the restricted pair. -/
def ofPair_hom {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (p : SpacePair Z X T) :
    (uliftSheaf T).obj ⟶ (homSheaf Z X).obj where
  app U := TypeCat.ofHom fun x ↦
    overEquiv Z X U.unop
      (SpacePair.map (yonedaEquiv.symm x.down : ofOver U.unop ⟶ T) p)
  naturality := sorry

/-- The sheaf morphism `T ⟶ Mor_B(Z, X)` associated to a pair `(a, b)` over `T`. -/
def ofPair {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (p : SpacePair Z X T) :
    uliftSheaf T ⟶ homSheaf Z X :=
  Sheaf.homEquiv.symm (ofPair_hom p)

/-- Components of `ofPair` restrict the algebraic-space pair along the underlying
`T`-point. -/
theorem ofPair_hom_app {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (p : SpacePair Z X T) (U : (Over S)ᵒᵖ)
    (x : ULift.{u + 1} (T.functorOfPoints.obj U)) :
    (ofPair p).hom.app U x =
      overEquiv Z X U.unop
        (SpacePair.map (yonedaEquiv.symm x.down : ofOver U.unop ⟶ T) p) :=
  sorry

/-- The morphism `a : T ⟶ B` recovered from a sheaf map `T ⟶ Mor_B(Z, X)` by the
structure morphism `Mor_B(Z, X) ⟶ B` and full faithfulness of universe lifting. -/
def toPair_a {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : uliftSheaf T ⟶ homSheaf Z X) : T ⟶ B :=
  (fullyFaithfulULiftFunctor.{u + 1, u}.whiskeringRight (Over S)ᵒᵖ).preimage
    (v ≫ toBase Z X).hom

/-- The scheme-level pair obtained by evaluating a sheaf map on a `T`-point. -/
def toPairEval {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : uliftSheaf T ⟶ homSheaf Z X) {U : (Over S)ᵒᵖ}
    (t : T.functorOfPoints.obj U) : HomPair Z X U.unop :=
  (v.hom.app U) (ULift.up t)

/-- The `T`-point of a `U`-point of `T ×_{a, B} Z`. -/
def toPairFst {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : uliftSheaf T ⟶ homSheaf Z X) {U : (Over S)ᵒᵖ}
    (x : (pullback (toPair_a v) Z.hom).functorOfPoints.obj U) :
    T.functorOfPoints.obj U :=
  (pullback.fst (toPair_a v) Z.hom).app U x

/-- The `Z`-point of a `U`-point of `T ×_{a, B} Z`. -/
def toPairSnd {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : uliftSheaf T ⟶ homSheaf Z X) {U : (Over S)ᵒᵖ}
    (x : (pullback (toPair_a v) Z.hom).functorOfPoints.obj U) :
    Z.left.functorOfPoints.obj U :=
  (pullback.snd (toPair_a v) Z.hom).app U x

/-- The canonical section of `U ×_{a_U, B} Z` over a `U`-point of `T ×_{a, B} Z`
lies over `B`. -/
theorem toPairSection_overB {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : uliftSheaf T ⟶ homSheaf Z X) {U : (Over S)ᵒᵖ}
    (x : (pullback (toPair_a v) Z.hom).functorOfPoints.obj U) :
    𝟙 (ofOver U.unop) ≫ (toPairEval v (toPairFst v x)).base =
      (yonedaEquiv.symm (toPairSnd v x) : ofOver U.unop ⟶ Z.left) ≫ Z.hom :=
  sorry

/-- The canonical section `U ⟶ U ×_{a_U, B} Z` of a `U`-point of `T ×_{a, B} Z`. -/
def toPairSection {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : uliftSheaf T ⟶ homSheaf Z X) {U : (Over S)ᵒᵖ}
    (x : (pullback (toPair_a v) Z.hom).functorOfPoints.obj U) :
    ofOver U.unop ⟶ pullback (toPairEval v (toPairFst v x)).base Z.hom :=
  pullback.lift (𝟙 _)
    (yonedaEquiv.symm (toPairSnd v x) : ofOver U.unop ⟶ Z.left)
    (toPairSection_overB v x)

/-- The morphism `T ×_{a, B} Z ⟶ X` recovered from a sheaf map
`T ⟶ Mor_B(Z, X)`. -/
def toPair_b {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : uliftSheaf T ⟶ homSheaf Z X) :
    pullback (toPair_a v) Z.hom ⟶ X.left where
  app U := TypeCat.ofHom fun x ↦
    yonedaEquiv
      (toPairSection v x ≫ HomPair.toOverMorph (toPairEval v (toPairFst v x)))
  naturality := sorry

/-- The morphism `toPair_b v` makes the triangle over `B` commute. -/
theorem toPair_b_over_base {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : uliftSheaf T ⟶ homSheaf Z X) :
    toPair_b v ≫ X.hom = pullback.fst (toPair_a v) Z.hom ≫ toPair_a v :=
  sorry

/-- The 05Y1 pair over `T` associated to a sheaf morphism `T ⟶ Mor_B(Z, X)`. -/
def toPair {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : uliftSheaf T ⟶ homSheaf Z X) :
    SpacePair Z X T :=
  SpacePair.ofOverMorph (toPair_a v) (toPair_b v) (toPair_b_over_base v)

/-- Sheaf morphisms `T ⟶ Mor_B(Z, X)` correspond to 05Y1 pairs over the algebraic
space `T`. -/
def homEquiv {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    (T : AlgebraicSpace S) :
    (uliftSheaf T ⟶ homSheaf Z X) ≃ SpacePair Z X T where
  toFun := toPair
  invFun := ofPair
  left_inv := sorry
  right_inv := sorry

/-- `homEquiv` sends a sheaf morphism to the associated pair. -/
theorem homEquiv_apply {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    {T : AlgebraicSpace S} (v : uliftSheaf T ⟶ homSheaf Z X) :
    homEquiv Z X T v = toPair v :=
  sorry

/-- The inverse of `homEquiv` sends a pair to the associated sheaf morphism. -/
theorem homEquiv_symm_apply {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    {T : AlgebraicSpace S} (p : SpacePair Z X T) :
    (homEquiv Z X T).symm p = ofPair p :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
