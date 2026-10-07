module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.CategoryTheory.Fibered.Stack.Prestack
public import stacks_project.Chap65.Lemma_65_7_1_Product
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap78.Lemma_78_20_2_Atlas

/-!
# Representing object of Isom on a quotient stack

This module constructs the algebraic space `S' ×_{(y', x')} R` representing morphisms in
`[U/_p R]` between two scheme-valued points of `U`, together with its relative sheaf of
points on `(Sch/S')_fppf` and the conversion of morphisms `S' ⟶ U` into objects of `𝒮_U`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The algebraic space `S' ×_{(y', x'), U ×_S U} R` obtained by pulling `R → U ×_S U` back
along `(y', x') : S' → U ×_S U`. The pairing is `(t, s)`, matching the source convention
that a point of `R` has target `y'` and source `x'`. -/
def isomPullback {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) : AlgebraicSpace S :=
  pullback (prod.lift y' x') (prod.lift G.t.left G.s.left)

/-- The structure morphism of `isomPullback G x' y'` to `S'` over `S`. -/
def isomPullback_fst {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) :
    isomPullback G x' y' ⟶ ofOver S' :=
  pullback.fst (prod.lift y' x') (prod.lift G.t.left G.s.left)

/-- The projection of `isomPullback G x' y'` to the arrow space `R`. -/
def isomPullback_snd {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) :
    isomPullback G x' y' ⟶ G.R.left :=
  pullback.snd (prod.lift y' x') (prod.lift G.t.left G.s.left)

/-- The two projections of `isomPullback G x' y'` agree in `U ×_S U`. -/
theorem isomPullback_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) :
    isomPullback_fst G x' y' ≫ prod.lift y' x' =
      isomPullback_snd G x' y' ≫ prod.lift G.t.left G.s.left :=
  sorry

/-- A morphism `T → R` over `S` is a `T`-point of `isomPullback G x' y'` over `S'` if and
only if it has target `T → S' → U` given by `y'` and source given by `x'`. -/
theorem mem_isomPullback_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left)
    {T : Over S} (φ : T ⟶ S') (r : ofOver T ⟶ G.R.left) :
    (∃ f : ofOver T ⟶ isomPullback G x' y',
        f ≫ isomPullback_fst G x' y' = ofOverMap φ ∧
          f ≫ isomPullback_snd G x' y' = r) ↔
      r ≫ G.t.left = ofOverMap φ ≫ y' ∧ r ≫ G.s.left = ofOverMap φ ≫ x' :=
  sorry

/-- A `T`-section of the relative points of `isomPullback G x' y'` over `S'`. -/
def isomPullbackSection {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left)
    (T : (Over S')ᵒᵖ) : Type (u + 1) :=
  { r : ofOver T.unop.left ⟶ G.R.left //
    r ≫ G.t.left = ofOverMap T.unop.hom ≫ y' ∧
      r ≫ G.s.left = ofOverMap T.unop.hom ≫ x' }

/-- Restrict a relative `R`-point along a morphism of schemes over `S'`. -/
def isomPullbackSection.restrict {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left)
    {T₁ T₂ : (Over S')ᵒᵖ} (φ : T₁ ⟶ T₂) (r : isomPullbackSection G x' y' T₁) :
    isomPullbackSection G x' y' T₂ :=
  ⟨ofOverMap φ.unop.left ≫ r.1, sorry⟩

/-- Restriction of a relative `R`-point is precomposition with `ofOverMap`. -/
theorem isomPullbackSection.restrict_arrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left)
    {T₁ T₂ : (Over S')ᵒᵖ} (φ : T₁ ⟶ T₂) (r : isomPullbackSection G x' y' T₁) :
    (isomPullbackSection.restrict G x' y' φ r).1 = ofOverMap φ.unop.left ≫ r.1 :=
  sorry

/-- The presheaf on `(Sch/S')_fppf` whose value at `T → S'` is the type of morphisms
`T → R` with target `T → S' → U` equal to `y'` and source equal to `x'`. -/
def isomPullbackPresheaf {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) :
    (Over S')ᵒᵖ ⥤ Type (u + 1) where
  obj T := isomPullbackSection G x' y' T
  map φ := TypeCat.ofHom (isomPullbackSection.restrict G x' y' φ)
  map_id := sorry
  map_comp := sorry

/-- Restriction of a section of `isomPullbackPresheaf` is precomposition with `ofOverMap`. -/
theorem isomPullbackPresheaf_map_arrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left)
    {T₁ T₂ : (Over S')ᵒᵖ} (φ : T₁ ⟶ T₂) (r : (isomPullbackPresheaf G x' y').obj T₁) :
    ((isomPullbackPresheaf G x' y').map φ r).1 = ofOverMap φ.unop.left ≫ r.1 :=
  sorry

/-- The relative points presheaf of `isomPullback G x' y'` is an fppf sheaf on `Sch/S'`. -/
theorem isomPullbackPresheaf_isSheaf {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) :
    Presheaf.IsSheaf ((Scheme.fppfTopology.over S).over S')
      (isomPullbackPresheaf G x' y') :=
  sorry

/-- The sheaf of `S'`-points of `S' ×_{(y', x'), U ×_S U} R` on `(Sch/S')_fppf`. -/
def isomPullbackSheaf {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) :
    Sheaf ((Scheme.fppfTopology.over S).over S') (Type (u + 1)) :=
  ⟨isomPullbackPresheaf G x' y', isomPullbackPresheaf_isSheaf G x' y'⟩

/-- The underlying presheaf of `isomPullbackSheaf G x' y'` is `isomPullbackPresheaf G x' y'`. -/
theorem isomPullbackSheaf_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) :
    (isomPullbackSheaf G x' y').obj = isomPullbackPresheaf G x' y' :=
  sorry

/-- A section of `isomPullbackSheaf G x' y'` over `T → S'` is an arrow of `R` with target
`y'` and source `x'` after restriction along `T → S'`. -/
theorem isomPullbackSheaf_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left)
    {T : Over S'} (s : (isomPullbackSheaf G x' y').obj.obj (op T)) :
    s.1 ≫ G.t.left = ofOverMap T.hom ≫ y' ∧
      s.1 ≫ G.s.left = ofOverMap T.hom ≫ x' :=
  sorry

/-- Convert a morphism `T → X` of algebraic spaces over `S` into the corresponding object of
the stack in sets `𝒮_X` over `T`, via the category-of-elements encoding of `stackInSets`. -/
def objOfHom {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S} (f : ofOver T ⟶ X) :
    (stackInSets X).p.Fiber T :=
  Functor.Fiber.mk
    (a := (op ⟨op T, yonedaEquiv (f : yoneda.obj T ⟶ X.functorOfPoints)⟩ :
      (stackInSets X).total))
    sorry

/-- The functor-of-points value stored by `objOfHom f` is the Yoneda transpose of `f`. -/
theorem objOfHom_spec {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (f : ofOver T ⟶ X) :
    yonedaEquiv (f : yoneda.obj T ⟶ X.functorOfPoints) = (objOfHom f).1.unop.snd :=
  sorry

/-- Before stackification, the Hom-presheaf of `[U/_p R]` between the images of `x'` and
`y'` is isomorphic to the sheaf of `S'`-points of `isomPullback G x' y'`. -/
theorem presheafHom_preQuotient_isIsomorphic_isomPullback
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) :
    IsIsomorphic
      ((Functor.fiberPseudofunctor (preQuotient G).p).presheafHom
        (((atlasToPreQuotient G).fiberFunctor S').obj (objOfHom x'))
        (((atlasToPreQuotient G).fiberFunctor S').obj (objOfHom y')))
      (isomPullbackSheaf G x' y').obj :=
  sorry
end AlgebraicGeometry.GroupoidAlgebraicSpace
