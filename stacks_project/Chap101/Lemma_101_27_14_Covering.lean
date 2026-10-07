module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Standard
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology

/-!
# Covering lifts of a family of 1-morphisms of groupoid fibrations

A family of 1-morphisms `f j : Xj j ⟶ X` of categories fibred in groupoids over
`(Sch/S)_fppf` admits a `τ`-covering family lift of an object `x` of `X` when
some `τ`-covering of the scheme over which `x` lives has an assignment into the
family index together with objects of the selected source stacks whose images
are `2`-isomorphic to the restrictions of `x`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.Groupoids.Hom

/-- Existence of a `τ`-covering of the scheme underlying `x` together with an
assignment `a` into the family index and objects `xi i` of `Xj (a i)` such that
`xi i ≫ f (a i)` is `2`-isomorphic to the restriction of `x` along each covering
map. -/
def existsCoveringFamilyLift (τ : StandardTopology) {S : Scheme.{u}}
    {J : Type v} {Xj : J → GroupoidsOver S} {X : GroupoidsOver S}
    (f : ∀ j, Xj j ⟶ X) {U : Over S} (x : GroupoidsOver.slice U ⟶ X) : Prop :=
  ∃ (I : Type u) (family : I → Over U.left) (a : I → J)
    (xi : ∀ i, GroupoidsOver.slice (Over.mk ((family i).hom ≫ U.hom)) ⟶ Xj (a i)),
    Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
        τ.precoverage.coverings U.left ∧
      ∀ i, Nonempty
        (xi i ≫ f (a i) ≅
          slice.pullback
            (Over.homMk (family i).hom rfl :
              Over.mk ((family i).hom ≫ U.hom) ⟶ U) x)

/-- Unfolding of `existsCoveringFamilyLift` as a `τ`-covering family of schemes
over `U.left`, an assignment into the family index, and `2`-isomorphic lifts of
the restrictions of `x`. -/
theorem existsCoveringFamilyLift_iff (τ : StandardTopology) {S : Scheme.{u}}
    {J : Type v} {Xj : J → GroupoidsOver S} {X : GroupoidsOver S}
    (f : ∀ j, Xj j ⟶ X) {U : Over S} (x : GroupoidsOver.slice U ⟶ X) :
    existsCoveringFamilyLift τ f x ↔
      ∃ (I : Type u) (family : I → Over U.left) (a : I → J)
        (xi : ∀ i, GroupoidsOver.slice (Over.mk ((family i).hom ≫ U.hom)) ⟶
          Xj (a i)),
        Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
            τ.precoverage.coverings U.left ∧
          ∀ i, Nonempty
            (xi i ≫ f (a i) ≅
              slice.pullback
                (Over.homMk (family i).hom rfl :
                  Over.mk ((family i).hom ≫ U.hom) ⟶ U) x) :=
  sorry

namespace existsCoveringFamilyLift

/-- A `τ`-covering family of `U.left` with an assignment into the family index
and `2`-isomorphic lifts of the restrictions of `x` witnesses
`existsCoveringFamilyLift`. -/
theorem of {τ : StandardTopology} {S : Scheme.{u}} {J : Type v}
    {Xj : J → GroupoidsOver S} {X : GroupoidsOver S} {f : ∀ j, Xj j ⟶ X}
    {U : Over S} {x : GroupoidsOver.slice U ⟶ X} {I : Type u}
    (family : I → Over U.left) (a : I → J)
    (xi : ∀ i, GroupoidsOver.slice (Over.mk ((family i).hom ≫ U.hom)) ⟶ Xj (a i))
    (h_covering :
      Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
        τ.precoverage.coverings U.left)
    (h_iso : ∀ i, Nonempty
      (xi i ≫ f (a i) ≅
        slice.pullback
          (Over.homMk (family i).hom rfl :
            Over.mk ((family i).hom ≫ U.hom) ⟶ U) x)) :
    existsCoveringFamilyLift τ f x :=
  sorry

/-- `existsCoveringFamilyLift τ f x` supplies a `τ`-covering of `U.left`, an
assignment into the family index, and objects of the selected source stacks
whose images under the corresponding `f (a i)` are `2`-isomorphic to the
restrictions of `x`. -/
theorem spec {τ : StandardTopology} {S : Scheme.{u}} {J : Type v}
    {Xj : J → GroupoidsOver S} {X : GroupoidsOver S} {f : ∀ j, Xj j ⟶ X}
    {U : Over S} {x : GroupoidsOver.slice U ⟶ X}
    (h : existsCoveringFamilyLift τ f x) :
    ∃ (I : Type u) (family : I → Over U.left) (a : I → J)
      (xi : ∀ i, GroupoidsOver.slice (Over.mk ((family i).hom ≫ U.hom)) ⟶
        Xj (a i)),
      Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
          τ.precoverage.coverings U.left ∧
        ∀ i, Nonempty
          (xi i ≫ f (a i) ≅
            slice.pullback
              (Over.homMk (family i).hom rfl :
                Over.mk ((family i).hom ≫ U.hom) ⟶ U) x) :=
  sorry

/-- `existsCoveringFamilyLift` for the fppf topology is equivalent to the
existence of an fppf covering family of `U.left` with an assignment into the
family index and `2`-isomorphic lifts. -/
theorem fppf_iff {S : Scheme.{u}} {J : Type v} {Xj : J → GroupoidsOver S}
    {X : GroupoidsOver S} (f : ∀ j, Xj j ⟶ X) {U : Over S}
    (x : GroupoidsOver.slice U ⟶ X) :
    existsCoveringFamilyLift StandardTopology.fppf f x ↔
      ∃ (I : Type u) (family : I → Over U.left) (a : I → J)
        (xi : ∀ i, GroupoidsOver.slice (Over.mk ((family i).hom ≫ U.hom)) ⟶
          Xj (a i)),
        Scheme.FppfCovering family ∧
          ∀ i, Nonempty
            (xi i ≫ f (a i) ≅
              slice.pullback
                (Over.homMk (family i).hom rfl :
                  Over.mk ((family i).hom ≫ U.hom) ⟶ U) x) :=
  sorry

end existsCoveringFamilyLift

end AlgebraicGeometry.Groupoids.Hom
