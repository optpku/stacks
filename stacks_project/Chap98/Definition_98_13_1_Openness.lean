/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.SliceBaseChange
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Composition
public import stacks_project.Chap98.Definition_98_13_1_Versal

/-!
# Openness of versality

A category fibred in groupoids over a locally Noetherian scheme satisfies
openness of versality when versality at a finite type point spreads to an open
neighbourhood of finite type points. A 1-morphism satisfies the same axiom
when every slice 2-fibre product does.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- A category `X` fibred in groupoids over `(Sch/S)_fppf` satisfies openness of
versality when versality of an object `x` over a locally finite type scheme `U`
at a finite type point `u0` spreads to every finite type point of some open
neighbourhood of `u0`. -/
class OpennessOfVersality {S : Scheme.{u}} [IsLocallyNoetherian S]
    (X : GroupoidsOver S) : Prop where
  /-- Versality at a finite type point spreads to an open neighbourhood. -/
  exists_nhd :
    ∀ {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
      (hx : X.p.obj x = Over.mk hU) (u0 : U), IsFiniteTypePoint u0 →
      IsVersalAt hU x hx u0 →
        ∃ U' : Opens U, u0 ∈ U' ∧
          ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt hU x hx u

/-- The 2-fibre product `(Sch/U)_fppf ×_Y X` associated to a 1-morphism
`f : X ⟶ Y` and an object `y` of `Y` over `U`, reindexed as a category fibred
in groupoids over `Over U`. -/
def fiberProductSlice {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {U : Scheme.{u}} (hU : U ⟶ S) (y : Y.total)
    (hy : Y.p.obj y = Over.mk hU) : GroupoidsOver U :=
  ⟨BasedCategory.ofFunctor
    ((FiberedCategoryOver.Groupoids.baseChange f (yonedaOfObject hU y hy)).p ⋙
      Over.iteratedSliceForward (Over.mk hU)), sorry⟩

/-- The total category of `fiberProductSlice f hU y hy` is the total category of
the slice base change along the 2-Yoneda 1-morphism of `y`. -/
theorem fiberProductSlice_total {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {U : Scheme.{u}} (hU : U ⟶ S) (y : Y.total)
    (hy : Y.p.obj y = Over.mk hU) :
    (fiberProductSlice f hU y hy).total =
      (FiberedCategoryOver.Groupoids.baseChange f (yonedaOfObject hU y hy)).total :=
  sorry

/-- `fiberProductSlice` is the slice base change of `f` along the 2-Yoneda
1-morphism of `y`, reindexed along `Over.iteratedSliceForward`. -/
theorem fiberProductSlice_spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {U : Scheme.{u}} (hU : U ⟶ S) (y : Y.total)
    (hy : Y.p.obj y = Over.mk hU) :
    (fiberProductSlice f hU y hy).toBasedCategory =
      BasedCategory.ofFunctor
        ((FiberedCategoryOver.Groupoids.baseChange f (yonedaOfObject hU y hy)).p ⋙
          Over.iteratedSliceForward (Over.mk hU)) :=
  sorry

namespace OpennessOfVersality

/-- The canonical slice fibration of a scheme over a locally Noetherian base
satisfies openness of versality. -/
instance slice {S : Scheme.{u}} [IsLocallyNoetherian S] (V : Over S) :
    OpennessOfVersality (GroupoidsOver.slice V) :=
  sorry

/-- Openness of versality supplies an open neighbourhood of finite type points
on which versality persists. -/
theorem spec {S : Scheme.{u}} [IsLocallyNoetherian S] (X : GroupoidsOver S)
    [OpennessOfVersality X] {U : Scheme.{u}} (hU : U ⟶ S)
    [LocallyOfFiniteType hU] (x : X.total) (hx : X.p.obj x = Over.mk hU)
    (u0 : U) (hu0 : IsFiniteTypePoint u0) (hvers : IsVersalAt hU x hx u0) :
    ∃ U' : Opens U, u0 ∈ U' ∧
      ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt hU x hx u :=
  sorry

/-- Openness of versality is the neighbourhood spreading of versality at finite
type points. -/
theorem iff {S : Scheme.{u}} [IsLocallyNoetherian S] (X : GroupoidsOver S) :
    OpennessOfVersality X ↔
      ∀ {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
        (hx : X.p.obj x = Over.mk hU) (u0 : U), IsFiniteTypePoint u0 →
        IsVersalAt hU x hx u0 →
          ∃ U' : Opens U, u0 ∈ U' ∧
            ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt hU x hx u :=
  sorry

end OpennessOfVersality

/-- Unfolding `OpennessOfVersality` recovers the neighbourhood quantifier. -/
theorem opennessOfVersality_iff {S : Scheme.{u}} [IsLocallyNoetherian S]
    (X : GroupoidsOver S) :
    OpennessOfVersality X ↔
      ∀ {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
        (hx : X.p.obj x = Over.mk hU) (u0 : U), IsFiniteTypePoint u0 →
        IsVersalAt hU x hx u0 →
          ∃ U' : Opens U, u0 ∈ U' ∧
            ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt hU x hx u :=
  sorry

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.Groupoids.Hom

open AlgebraicGeometry.GroupoidsOver

/-- A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over
`(Sch/S)_fppf` satisfies openness of versality when every slice 2-fibre product
`(Sch/U)_fppf ×_Y X` does. -/
class OpennessOfVersality {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X Y : GroupoidsOver S} (f : X ⟶ Y) : Prop where
  /-- Every slice 2-fibre product satisfies openness of versality. -/
  ofBaseChange :
    ∀ {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
      [IsLocallyNoetherian U] (y : Y.total) (hy : Y.p.obj y = Over.mk hU),
      GroupoidsOver.OpennessOfVersality (fiberProductSlice f hU y hy)

namespace OpennessOfVersality

/-- The identity 1-morphism of a category fibred in groupoids satisfies openness
of versality. -/
instance id {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S} :
    OpennessOfVersality (𝟙 X) :=
  sorry

/-- Openness of versality of `f` means every slice 2-fibre product satisfies
openness of versality. -/
theorem spec {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [OpennessOfVersality f] {U : Scheme.{u}} (hU : U ⟶ S)
    [LocallyOfFiniteType hU] [IsLocallyNoetherian U] (y : Y.total)
    (hy : Y.p.obj y = Over.mk hU) :
    GroupoidsOver.OpennessOfVersality (fiberProductSlice f hU y hy) :=
  sorry

/-- Openness of versality of a 1-morphism is openness of versality of every
slice 2-fibre product. -/
theorem iff {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    OpennessOfVersality f ↔
      ∀ {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
        [IsLocallyNoetherian U] (y : Y.total) (hy : Y.p.obj y = Over.mk hU),
        GroupoidsOver.OpennessOfVersality (fiberProductSlice f hU y hy) :=
  sorry

end OpennessOfVersality

/-- Unfolding morphism-level `OpennessOfVersality` recovers the 2-fibre product
reduction. -/
theorem opennessOfVersality_iff {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    OpennessOfVersality f ↔
      ∀ {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
        [IsLocallyNoetherian U] (y : Y.total) (hy : Y.p.obj y = Over.mk hU),
        GroupoidsOver.OpennessOfVersality (fiberProductSlice f hU y hy) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
