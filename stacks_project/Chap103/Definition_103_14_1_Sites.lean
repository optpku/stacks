/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import stacks_project.Chap07.Definition_7_6_2_Site
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import stacks_project.Chap100.Lemma_100_11_1_Flat

/-!
# Lisse-étale and flat-fppf sites of an algebraic stack

The lisse-étale site of an algebraic stack `X` is the full subcategory of `X`
on objects whose 2-Yoneda 1-morphism is smooth, with coverings inherited from
the associated étale site. The flat-fppf site is the analogous full subcategory
on flat 1-morphisms, with coverings inherited from the associated fppf site.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open FiberedCategoryOver.Groupoids.YonedaSlice
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The 2-Yoneda 1-morphism `x : U ⟶ X` associated to an object `x` of `X`
lying over a scheme `U`. -/
def yonedaHom (X : GroupoidsOver S) (x : X.total) :
    slice (X.p.obj x) ⟶ X :=
  representative ⟨x, rfl⟩

/-- `yonedaHom X x` is the groupoid-fibred Yoneda representative of the fiber
object `⟨x, rfl⟩`. -/
theorem yonedaHom_spec (X : GroupoidsOver S) (x : X.total) :
    yonedaHom X x = representative ⟨x, rfl⟩ := sorry

/-- Evaluate a 1-morphism `f : slice U ⟶ X` at the identity object of `U`. -/
def evalId {X : GroupoidsOver S} {U : Over S} (f : GroupoidsOver.slice U ⟶ X) : X.total :=
  Functor.Fiber.fiberInclusion.obj
    ((FiberedCategoryOver.Groupoids.fiberFunctor f U).obj
      (BasedCategory.Yoneda.Identity.fiberObj U))

/-- `evalId f` is the image of the identity slice object under the fiber functor
of `f`. -/
theorem evalId_eq {X : GroupoidsOver S} {U : Over S} (f : GroupoidsOver.slice U ⟶ X) :
    evalId f =
      Functor.Fiber.fiberInclusion.obj
        ((FiberedCategoryOver.Groupoids.fiberFunctor f U).obj
          (BasedCategory.Yoneda.Identity.fiberObj U)) :=
  sorry

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.AlgebraicStack

open GroupoidsOver

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]

/-- Objects of `X` whose 2-Yoneda 1-morphism `U ⟶ X` is smooth. -/
def isLisse : ObjectProperty X.total :=
  fun x ↦ Groupoids.Hom.Smooth (yonedaHom X x)

/-- An object of `X` is lisse if and only if `yonedaHom X x` is smooth. -/
theorem isLisse_iff (x : X.total) :
    isLisse X x ↔ Groupoids.Hom.Smooth (yonedaHom X x) := sorry

/-- Objects of `X` whose 2-Yoneda 1-morphism `U ⟶ X` is flat. -/
def isFlat : ObjectProperty X.total :=
  fun x ↦ Groupoids.Hom.Flat (yonedaHom X x)

/-- An object of `X` is flat over `X` if and only if `yonedaHom X x` is flat. -/
theorem isFlat_iff (x : X.total) :
    isFlat X x ↔ Groupoids.Hom.Flat (yonedaHom X x) := sorry

/-- The underlying category of the lisse-étale site of `X`. -/
abbrev lisseEtaleSite := (isLisse X).FullSubcategory

/-- The lisse-étale site category is the full subcategory of lisse objects of
`X`. -/
theorem lisseEtaleSite_eq : lisseEtaleSite X = (isLisse X).FullSubcategory :=
  sorry

/-- Pack a lisse object of `X` as an object of the lisse-étale site. -/
def lisseEtaleSite.mk {x : X.total} (hx : isLisse X x) : lisseEtaleSite X :=
  ⟨x, hx⟩

/-- The underlying object of `lisseEtaleSite.mk hx` is `x`. -/
theorem lisseEtaleSite.mk_obj {x : X.total} (hx : isLisse X x) :
    (lisseEtaleSite.mk X hx).obj = x := sorry

/-- The object of the lisse-étale site presented by a smooth 1-morphism
`f : slice U ⟶ X`. -/
def lisseEtaleSite.ofHom {U : Over S} (f : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth f] :
    lisseEtaleSite X :=
  ⟨evalId f, sorry⟩

/-- The underlying object of `lisseEtaleSite.ofHom f` is `evalId f`. -/
theorem lisseEtaleSite.ofHom_obj {U : Over S}
    (f : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth f] :
    (lisseEtaleSite.ofHom X f).obj = evalId f := sorry

/-- The inclusion of the lisse-étale site of `X` into the total category of
`X`. -/
abbrev lisseEtaleInclusion : lisseEtaleSite X ⥤ X.total :=
  (isLisse X).ι

/-- The lisse-étale inclusion is the full-subcategory inclusion of `isLisse X`. -/
theorem lisseEtaleInclusion_eq :
    lisseEtaleInclusion X = (isLisse X).ι := sorry

/-- Covering families of the lisse-étale site are the associated étale covering
families of `X`, pulled back along the inclusion. -/
def lisseEtalePrecoverage : Precoverage (lisseEtaleSite X) :=
  X.etaleTopology.toPrecoverage.comap (lisseEtaleInclusion X)

/-- The lisse-étale precoverage is the comap of the associated étale precoverage
along the inclusion. -/
theorem lisseEtalePrecoverage_eq :
    lisseEtalePrecoverage X =
      X.etaleTopology.toPrecoverage.comap (lisseEtaleInclusion X) :=
  sorry

/-- A family in the lisse-étale site is covering if and only if its image is
covering in the associated étale site of `X`. -/
theorem ofArrows_mem_lisseEtalePrecoverage_iff {ι : Type u}
    {x : lisseEtaleSite X} {y : ι → lisseEtaleSite X} {f : ∀ i, y i ⟶ x} :
    Presieve.ofArrows y f ∈ lisseEtalePrecoverage X x ↔
      Presieve.ofArrows (fun i ↦ (lisseEtaleInclusion X).obj (y i))
          (fun i ↦ (lisseEtaleInclusion X).map (f i)) ∈
        X.etaleTopology.toPrecoverage ((lisseEtaleInclusion X).obj x) :=
  sorry

/-- The lisse-étale topology of an algebraic stack `X`. -/
def lisseEtaleTopology : GrothendieckTopology (lisseEtaleSite X) :=
  (lisseEtalePrecoverage X).toGrothendieck

/-- The lisse-étale topology is generated by the lisse-étale precoverage. -/
theorem lisseEtaleTopology_def :
    lisseEtaleTopology X = (lisseEtalePrecoverage X).toGrothendieck := sorry

/-- Lisse-étale covering families satisfy the site axioms. -/
instance lisseEtalePrecoverage.instIsSite :
    (lisseEtalePrecoverage X).IsSite := sorry

/-- The underlying category of the flat-fppf site of `X`. -/
abbrev flatFppfSite := (isFlat X).FullSubcategory

/-- The flat-fppf site category is the full subcategory of flat objects of
`X`. -/
theorem flatFppfSite_eq : flatFppfSite X = (isFlat X).FullSubcategory := sorry

/-- Pack a flat object of `X` as an object of the flat-fppf site. -/
def flatFppfSite.mk {x : X.total} (hx : isFlat X x) : flatFppfSite X :=
  ⟨x, hx⟩

/-- The underlying object of `flatFppfSite.mk hx` is `x`. -/
theorem flatFppfSite.mk_obj {x : X.total} (hx : isFlat X x) :
    (flatFppfSite.mk X hx).obj = x := sorry

/-- The object of the flat-fppf site presented by a flat 1-morphism
`f : slice U ⟶ X`. -/
def flatFppfSite.ofHom {U : Over S} (f : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Flat f] :
    flatFppfSite X :=
  ⟨evalId f, sorry⟩

/-- The underlying object of `flatFppfSite.ofHom f` is `evalId f`. -/
theorem flatFppfSite.ofHom_obj {U : Over S}
    (f : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Flat f] :
    (flatFppfSite.ofHom X f).obj = evalId f := sorry

/-- The inclusion of the flat-fppf site of `X` into the total category of `X`. -/
abbrev flatFppfInclusion : flatFppfSite X ⥤ X.total :=
  (isFlat X).ι

/-- The flat-fppf inclusion is the full-subcategory inclusion of `isFlat X`. -/
theorem flatFppfInclusion_eq : flatFppfInclusion X = (isFlat X).ι := sorry

/-- Covering families of the flat-fppf site are the associated fppf covering
families of `X`, pulled back along the inclusion. -/
def flatFppfPrecoverage : Precoverage (flatFppfSite X) :=
  X.fppfTopology.toPrecoverage.comap (flatFppfInclusion X)

/-- The flat-fppf precoverage is the comap of the associated fppf precoverage
along the inclusion. -/
theorem flatFppfPrecoverage_eq :
    flatFppfPrecoverage X =
      X.fppfTopology.toPrecoverage.comap (flatFppfInclusion X) :=
  sorry

/-- A family in the flat-fppf site is covering if and only if its image is
covering in the associated fppf site of `X`. -/
theorem ofArrows_mem_flatFppfPrecoverage_iff {ι : Type u}
    {x : flatFppfSite X} {y : ι → flatFppfSite X} {f : ∀ i, y i ⟶ x} :
    Presieve.ofArrows y f ∈ flatFppfPrecoverage X x ↔
      Presieve.ofArrows (fun i ↦ (flatFppfInclusion X).obj (y i))
          (fun i ↦ (flatFppfInclusion X).map (f i)) ∈
        X.fppfTopology.toPrecoverage ((flatFppfInclusion X).obj x) :=
  sorry

/-- The flat-fppf topology of an algebraic stack `X`. -/
def flatFppfTopology : GrothendieckTopology (flatFppfSite X) :=
  (flatFppfPrecoverage X).toGrothendieck

/-- The flat-fppf topology is generated by the flat-fppf precoverage. -/
theorem flatFppfTopology_def :
    flatFppfTopology X = (flatFppfPrecoverage X).toGrothendieck := sorry

/-- Flat-fppf covering families satisfy the site axioms. -/
instance flatFppfPrecoverage.instIsSite :
    (flatFppfPrecoverage X).IsSite := sorry

end AlgebraicGeometry.AlgebraicStack
