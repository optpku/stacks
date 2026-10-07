module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Bicategorical
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.OfPresheaf
public import ReasLib.CategoryTheory.Fibered.Groupoids.SliceBaseChange
public import ReasLib.CategoryTheory.Fibered.InSets.Slice
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver

/-!
# Categories fibred in groupoids representable by algebraic spaces

An algebraic space over a scheme `S` determines a category fibred in groupoids
over `Over S` by the discrete Grothendieck construction of its functor of points.
A morphism of such fibrations is representable by algebraic spaces when every
slice base change is equivalent to an algebraic space over `S` mapping to the
test scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver BasedFunctor BasedNatIso
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Categories fibred in groupoids over the big fppf site `(Sch/S)_fppf`. -/
abbrev GroupoidsOver (S : Scheme.{u}) :=
  FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)

/-- `GroupoidsOver S` is the universe-pinned bicategory of groupoid fibrations
over `Over S`. -/
theorem GroupoidsOver_eq (S : Scheme.{u}) :
    GroupoidsOver S = FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S) :=
  sorry

/-- The canonical slice of a scheme over `S`, as an object of `GroupoidsOver S`. -/
abbrev GroupoidsOver.slice {S : Scheme.{u}} (U : Over S) : GroupoidsOver S :=
  FiberedCategoryOver.Groupoids.slice U

/-- `GroupoidsOver.slice U` is the canonical slice fibration of `U`. -/
theorem GroupoidsOver.slice_eq {S : Scheme.{u}} (U : Over S) :
    GroupoidsOver.slice U = FiberedCategoryOver.Groupoids.slice U := sorry

namespace AlgebraicSpace

/-- The category fibred in groupoids associated to an algebraic space, obtained by
applying the discrete Grothendieck construction to its functor of points and
forgetting from sets to groupoids. -/
def toGroupoids {S : Scheme.{u}} (F : AlgebraicSpace S) : GroupoidsOver S :=
  (Sets.toGroupoids (Over S)).obj ((Sets.ofPresheaf (Over S)).obj F.functorOfPoints)

/-- A morphism of algebraic spaces induces a 1-morphism of the associated
categories fibred in groupoids. -/
def toGroupoids.map {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G) :
    F.toGroupoids ⟶ G.toGroupoids :=
  (Sets.toGroupoids (Over S)).map ((Sets.ofPresheaf (Over S)).map f)

/-- The groupoid fibration of an algebraic space is the discrete Grothendieck
construction of its functor of points, forgotten to groupoids. -/
theorem toGroupoids_spec {S : Scheme.{u}} (F : AlgebraicSpace S) :
    F.toGroupoids =
      (Sets.toGroupoids (Over S)).obj
        ((Sets.ofPresheaf (Over S)).obj F.functorOfPoints) := sorry

/-- The projection of `toGroupoids F` is the opposite category-of-elements
projection of the functor of points. -/
theorem toGroupoids_p {S : Scheme.{u}} (F : AlgebraicSpace S) :
    F.toGroupoids.p = ((Sets.ofPresheaf (Over S)).obj F.functorOfPoints).p := sorry

/-- `toGroupoids.map` sends identity morphisms of algebraic spaces to identity
1-morphisms. -/
theorem toGroupoids.map_id {S : Scheme.{u}} (F : AlgebraicSpace S) :
    toGroupoids.map (𝟙 F) = 𝟙 F.toGroupoids := sorry

/-- The groupoid fibration of a scheme over `S` is canonically equivalent to the
slice fibration, by applying `Sets.toGroupoids` to the set-fibred comparison of
`ofPresheaf (yoneda.obj U)` with `Sets.slice U`. -/
def ofOverSliceEquiv {S : Scheme.{u}} (U : Over S) :
    (ofOver U).toGroupoids ≌ GroupoidsOver.slice U :=
  let homBF :
      BasedFunctor
        ((Sets.ofPresheaf (Over S)).obj (yoneda.obj U)).toBasedCategory
        (Sets.slice U).toBasedCategory :=
    { obj := fun x ↦ Over.mk x.unop.2
      map := fun f ↦ Over.homMk f.unop.1.unop sorry
      map_id := sorry
      map_comp := sorry
      w := sorry }
  let invBF :
      BasedFunctor (Sets.slice U).toBasedCategory
        ((Sets.ofPresheaf (Over S)).obj (yoneda.obj U)).toBasedCategory :=
    { obj := fun α ↦ Opposite.op ⟨Opposite.op α.left, α.hom⟩
      map := fun {α β} κ ↦
        Quiver.Hom.op
          (CategoryOfElements.homMk
            (⟨Opposite.op β.left, β.hom⟩ : (yoneda.obj U).Elements)
            (⟨Opposite.op α.left, α.hom⟩ : (yoneda.obj U).Elements)
            κ.left.op sorry)
      map_id := sorry
      map_comp := sorry
      w := sorry }
  let qi : BasedFunctor.QuasiInverse homBF :=
    { inverse := invBF
      unitIso := BasedNatIso.ofComponents (fun x ↦ Iso.refl _) sorry sorry
      counitIso := BasedNatIso.ofComponents (fun α ↦ Iso.refl _) sorry sorry }
  (Sets.toGroupoids (Over S)).mapEquivalence
    (Bicategory.InducedBicategory.equivalenceMk qi.toEquivalence)

/-- The unit of `ofOverSliceEquiv` identifies the composite of the comparison with
its inverse. -/
theorem ofOverSliceEquiv_hom {S : Scheme.{u}} (U : Over S) :
    Nonempty
      ((ofOverSliceEquiv U).hom ≫ (ofOverSliceEquiv U).inv ≅
        𝟙 (ofOver U).toGroupoids) := sorry

/-- The groupoid fibration of a scheme over `S` is equivalent to the canonical
slice fibration. -/
theorem toGroupoids_ofOver {S : Scheme.{u}} (U : Over S) :
    Nonempty ((ofOver U).toGroupoids ≌ GroupoidsOver.slice U) := sorry

end AlgebraicSpace

open AlgebraicSpace

/-- A category fibred in groupoids over `(Sch/S)_fppf` is representable by an
algebraic space over `S` when it is equivalent to the Grothendieck construction
of some algebraic space over `S`. -/
def IsRepresentableByAlgebraicSpace {S : Scheme.{u}} :
    ObjectProperty (GroupoidsOver S) :=
  fun X ↦ ∃ F : AlgebraicSpace S, Nonempty (X ≌ F.toGroupoids)

/-- Representability by an algebraic space is equivalent to the existence of an
algebraic space and a bicategorical equivalence to its groupoid fibration. -/
theorem IsRepresentableByAlgebraicSpace.iff_exists_equivalence
    {S : Scheme.{u}} (X : GroupoidsOver S) :
    IsRepresentableByAlgebraicSpace X ↔
      ∃ F : AlgebraicSpace S, Nonempty (X ≌ F.toGroupoids) := sorry

/-- The groupoid fibration of an algebraic space is representable by that
algebraic space. -/
theorem IsRepresentableByAlgebraicSpace.of_toGroupoids
    {S : Scheme.{u}} (F : AlgebraicSpace S) :
    IsRepresentableByAlgebraicSpace F.toGroupoids := sorry

/-- A slice 2-fibre product of `f` along `y : GroupoidsOver.slice U ⟶ Y` is
represented by an algebraic space `Fy` over `S` with structure morphism
`fy : Fy ⟶ ofOver U` when the apex is equivalent to `Fy.toGroupoids` and the
projection triangle identifies `toGroupoids.map fy` with `TwoFibreProduct.fst`
along `ofOverSliceEquiv`. -/
def RepresentsBaseChange {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
    (fy : Fy ⟶ ofOver U) : Prop :=
  ∃ e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f ≌ Fy.toGroupoids,
    Nonempty
      (e.hom ≫ toGroupoids.map fy ≫ (ofOverSliceEquiv U).hom ≅
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} y f)

/-- A representing algebraic space is equivalent to the slice 2-fibre product. -/
theorem RepresentsBaseChange.apex_equivalence {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {f : X ⟶ Y} {U : Over S}
    {y : GroupoidsOver.slice U ⟶ Y} {Fy : AlgebraicSpace S} {fy : Fy ⟶ ofOver U}
    (h : RepresentsBaseChange f y Fy fy) :
    Nonempty (TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f ≌ Fy.toGroupoids) := sorry

/-- The structure morphism of a representing algebraic space recovers the
projection of the slice 2-fibre product along `ofOverSliceEquiv`. -/
theorem RepresentsBaseChange.projection_triangle {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {f : X ⟶ Y} {U : Over S}
    {y : GroupoidsOver.slice U ⟶ Y} {Fy : AlgebraicSpace S} {fy : Fy ⟶ ofOver U}
    (h : RepresentsBaseChange f y Fy fy) :
    ∃ e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f ≌ Fy.toGroupoids,
      Nonempty
        (e.hom ≫ toGroupoids.map fy ≫ (ofOverSliceEquiv U).hom ≅
          TwoFibreProduct.fst.{u + 1, u, u + 1, u} y f) :=
  sorry

/-- A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` is
representable by algebraic spaces when every base change along a morphism from a
canonical slice is representable by an algebraic space over `S`. -/
def relativelyRepresentableByAlgebraicSpaces {S : Scheme.{u}} :
    MorphismProperty (GroupoidsOver S) :=
  fun _ Y f ↦ ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y),
    ∃ (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver U), RepresentsBaseChange f y Fy fy

/-- Relative representability by algebraic spaces means every slice base change
is represented by an algebraic space over `S`. -/
theorem relativelyRepresentableByAlgebraicSpaces.iff {S : Scheme.{u}}
    {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    relativelyRepresentableByAlgebraicSpaces f ↔
      ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y),
        ∃ (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver U),
          RepresentsBaseChange f y Fy fy := sorry

/-- A relatively representable 1-morphism has a representing algebraic space for
every slice test. -/
theorem relativelyRepresentableByAlgebraicSpaces.exists_represents {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) {U : Over S}
    (y : GroupoidsOver.slice U ⟶ Y) :
    ∃ (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver U),
      RepresentsBaseChange f y Fy fy := sorry

/-- Relative representability by algebraic spaces follows from a representing
algebraic space for every slice test. -/
theorem relativelyRepresentableByAlgebraicSpaces.of_represents {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {f : X ⟶ Y}
    (h : ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y),
      ∃ (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver U),
        RepresentsBaseChange f y Fy fy) :
    relativelyRepresentableByAlgebraicSpaces f := sorry

end AlgebraicGeometry

