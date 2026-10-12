/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import stacks_project.Chap96.Lemma_96_12_4_EtaleModules
public import stacks_project.Chap96.Lemma_96_12_5_Comparison

/-!
# Restriction of quasi-coherent modules to small étale sites of objects

A 1-morphism `f : GroupoidsOver.slice U ⟶ X` is evaluated at the identity object
of the slice to produce an object of `X`. Restriction of a quasi-coherent
module along that object is transport to étale modules followed by restriction
to the small étale site of `p(x)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The object of `X` obtained by evaluating a slice 1-morphism at the identity
object of `U`. -/
def objectOfHom {X : GroupoidsOver S} {U : Over S}
    (f : GroupoidsOver.slice U ⟶ X) : X.total :=
  (FiberedCategoryOver.Groupoids.toFunctor f).obj (Over.mk (𝟙 U))

/-- The projection of `objectOfHom f` recovers the test scheme `U`. -/
theorem objectOfHom_p {X : GroupoidsOver S} {U : Over S}
    (f : GroupoidsOver.slice U ⟶ X) :
    X.p.obj (objectOfHom f) = U :=
  sorry

namespace QCoh

/-- Restriction of a quasi-coherent module along an object `x` of `X` to the
small étale site of `p(x)`. -/
def restrictToSmallEtale (X : GroupoidsOver S) (x : X.total) :
    QCoh X ⥤ RingedSite.ModuleCat.{u}
      (Scheme.Etale.Small.ringedSite (X.p.obj x).left) :=
  toEtaleModules X ⋙ restrictModulesToSmallEtale X x

/-- `restrictToSmallEtale` is étale transport followed by small-étale
restriction. -/
theorem restrictToSmallEtale_eq (X : GroupoidsOver S) (x : X.total) :
    restrictToSmallEtale X x =
      toEtaleModules X ⋙ restrictModulesToSmallEtale X x :=
  sorry

end QCoh

end AlgebraicGeometry.GroupoidsOver
