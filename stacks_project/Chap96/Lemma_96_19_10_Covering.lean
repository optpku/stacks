/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.CoveringLift

/-!
# Covering lifts of 1-morphisms of groupoid fibrations

A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over `(Sch/S)_fppf`
admits a `τ`-covering lift of an object `y` of `Y` when some `τ`-covering of
the scheme over which `y` lives has objects of `X` whose images under `f` are
`2`-isomorphic to the restrictions of `y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/- Existence of a `τ`-covering of the scheme underlying `y` together with
objects `x i` of `X` such that `x i ≫ f` is `2`-isomorphic to the restriction
of `y` along each covering map. -/
#check (AlgebraicGeometry.Groupoids.Hom.existsCoveringLift :
  StandardTopology → ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S},
    (X ⟶ Y) → ∀ {U : Over S}, (GroupoidsOver.slice U ⟶ Y) → Prop)

/- Unfolding of `existsCoveringLift` as a `τ`-covering family of schemes over
`U.left` together with `2`-isomorphic lifts of the restrictions of `y`. -/
#check (AlgebraicGeometry.Groupoids.Hom.existsCoveringLift_iff :
  ∀ (τ : StandardTopology) {S : Scheme.{u}}
    {X Y : GroupoidsOver S} (f : X ⟶ Y) {U : Over S}
    (y : GroupoidsOver.slice U ⟶ Y),
    existsCoveringLift τ f y ↔
      ∃ (ι : Type u) (family : ι → Over U.left)
        (x : ∀ i, GroupoidsOver.slice (Over.mk ((family i).hom ≫ U.hom)) ⟶ X),
        Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
            τ.precoverage.coverings U.left ∧
          ∀ i, Nonempty
            (x i ≫ f ≅
              slice.pullback
                (Over.homMk (family i).hom rfl :
                  Over.mk ((family i).hom ≫ U.hom) ⟶ U) y))

namespace existsCoveringLift

/- A `τ`-covering family of `U.left` with `2`-isomorphic lifts of the
restrictions of `y` witnesses `existsCoveringLift`. -/
#check (AlgebraicGeometry.Groupoids.Hom.existsCoveringLift.of :
  ∀ {τ : StandardTopology} {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {f : X ⟶ Y} {U : Over S} {y : GroupoidsOver.slice U ⟶ Y} {ι : Type u}
    (family : ι → Over U.left)
    (x : ∀ i, GroupoidsOver.slice (Over.mk ((family i).hom ≫ U.hom)) ⟶ X),
    Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
        τ.precoverage.coverings U.left →
    (∀ i, Nonempty
      (x i ≫ f ≅
        slice.pullback
          (Over.homMk (family i).hom rfl :
            Over.mk ((family i).hom ≫ U.hom) ⟶ U) y)) →
    existsCoveringLift τ f y)

/- `existsCoveringLift τ f y` supplies a `τ`-covering of `U.left` and objects
of `X` whose images under `f` are `2`-isomorphic to the restrictions of `y`. -/
#check (AlgebraicGeometry.Groupoids.Hom.existsCoveringLift.spec :
  ∀ {τ : StandardTopology} {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {f : X ⟶ Y} {U : Over S} {y : GroupoidsOver.slice U ⟶ Y},
    existsCoveringLift τ f y → ∃ (ι : Type u) (family : ι → Over U.left)
      (x : ∀ i, GroupoidsOver.slice (Over.mk ((family i).hom ≫ U.hom)) ⟶ X),
      Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
          τ.precoverage.coverings U.left ∧
        ∀ i, Nonempty
          (x i ≫ f ≅
            slice.pullback
              (Over.homMk (family i).hom rfl :
                Over.mk ((family i).hom ≫ U.hom) ⟶ U) y))

/- Membership of an indexed family in the fppf precoverage is the scheme-level
`FppfCovering` predicate. -/
#check (AlgebraicGeometry.Groupoids.Hom.existsCoveringLift.fppfCovering :
  ∀ {S : Scheme.{u}} {U : Over S} {ι : Type u}
    (family : ι → Over U.left),
    Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
        StandardTopology.fppf.precoverage.coverings U.left ↔
      Scheme.FppfCovering family)

/- Membership of an indexed family in the étale precoverage is the scheme-level
`EtaleCovering` predicate. -/
#check (AlgebraicGeometry.Groupoids.Hom.existsCoveringLift.etaleCovering :
  ∀ {S : Scheme.{u}} {U : Over S} {ι : Type u}
    (family : ι → Over U.left),
    Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
        StandardTopology.etale.precoverage.coverings U.left ↔
      Scheme.EtaleCovering family)

/- `existsCoveringLift` for the fppf topology is equivalent to the existence of
an fppf covering family of `U.left` with `2`-isomorphic lifts. -/
#check (AlgebraicGeometry.Groupoids.Hom.existsCoveringLift.fppf_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y),
    existsCoveringLift StandardTopology.fppf f y ↔
      ∃ (ι : Type u) (family : ι → Over U.left)
        (x : ∀ i, GroupoidsOver.slice (Over.mk ((family i).hom ≫ U.hom)) ⟶ X),
        Scheme.FppfCovering family ∧
          ∀ i, Nonempty
            (x i ≫ f ≅
              slice.pullback
                (Over.homMk (family i).hom rfl :
                  Over.mk ((family i).hom ≫ U.hom) ⟶ U) y))

/- `existsCoveringLift` for the étale topology is equivalent to the existence of
an étale covering family of `U.left` with `2`-isomorphic lifts. -/
#check (AlgebraicGeometry.Groupoids.Hom.existsCoveringLift.etale_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y),
    existsCoveringLift StandardTopology.etale f y ↔
      ∃ (ι : Type u) (family : ι → Over U.left)
        (x : ∀ i, GroupoidsOver.slice (Over.mk ((family i).hom ≫ U.hom)) ⟶ X),
        Scheme.EtaleCovering family ∧
          ∀ i, Nonempty
            (x i ≫ f ≅
              slice.pullback
                (Over.homMk (family i).hom rfl :
                  Over.mk ((family i).hom ≫ U.hom) ⟶ U) y))

/- A covering lift of `y` induces a covering of `U` in the big `τ`-site of `S`,
together with objects whose images are `2`-isomorphic to the restrictions of `y`. -/
#check (AlgebraicGeometry.Groupoids.Hom.existsCoveringLift.mem_associatedTopology :
  ∀ {τ : StandardTopology} {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {f : X ⟶ Y} {U : Over S}
    {y : GroupoidsOver.slice U ⟶ Y},
    existsCoveringLift τ f y → ∃ (ι : Type u) (family : ι → Over U.left)
      (x : ∀ i, GroupoidsOver.slice (Over.mk ((family i).hom ≫ U.hom)) ⟶ X),
      Sieve.generate
          (Presieve.ofArrows (fun i ↦ Over.mk ((family i).hom ≫ U.hom))
            (fun i ↦ Over.homMk (family i).hom rfl)) ∈
        StandardTopology.overTopology τ S U ∧
      ∀ i, Nonempty
        (x i ≫ f ≅
          slice.pullback
            (Over.homMk (family i).hom rfl :
              Over.mk ((family i).hom ≫ U.hom) ⟶ U) y))

end existsCoveringLift

end AlgebraicGeometry.Groupoids.Hom
