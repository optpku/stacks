/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Lemma_74_23_1_SheafDescent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

/- Lemma 74.23.1 (1): for a scheme `S` and an fppf covering `{Xᵢ → X}` of algebraic spaces
over `S`, descent data `(Vᵢ, φᵢⱼ)` relative to the covering are equivalent to sheaves
`F` on `(Sch/S)_fppf` endowed with a map `F ⟶ X` such that each `Xᵢ ×_X F` is an
algebraic space. -/
@[stacks 0ADT] #check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.sheafEquivalence :
    ∀ {I : Type v} {S : Scheme.{u}} {X : AlgebraicSpace S}
      (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)
      [Small.{u} I] [AlgebraicGeometry.AlgebraicSpace.FppfCovering Xᵢ f],
      AlgebraicGeometry.AlgebraicSpace.DescentData Xᵢ f ≌
        AlgebraicGeometry.AlgebraicSpace.DescentData.LocallyAlgebraicSpaceAlong Xᵢ f)

/- Lemma 74.23.1 (2): under the equivalence, `Xᵢ ×_X F` corresponds to `Vᵢ`. -/
@[stacks 0ADT] #check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.productIso :
    ∀ {I : Type v} {S : Scheme.{u}} {X : AlgebraicSpace S}
      (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)
      [Small.{u} I] [AlgebraicGeometry.AlgebraicSpace.FppfCovering Xᵢ f]
      (D : AlgebraicGeometry.AlgebraicSpace.DescentData Xᵢ f) (i : I),
      D.obj i ≅
        (AlgebraicGeometry.AlgebraicSpace.DescentData.fromSheafObj Xᵢ f
            ((AlgebraicGeometry.AlgebraicSpace.DescentData.glue Xᵢ f).obj D)).obj i)

/- Lemma 74.23.1 (3): `F` is an algebraic space if and only if the corresponding
descent datum is effective. -/
@[stacks 0ADT] #check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.isAlgebraicSpace_iff_effective :
    ∀ {I : Type v} {S : Scheme.{u}} {X : AlgebraicSpace S}
      (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)
      [Small.{u} I] [AlgebraicGeometry.AlgebraicSpace.FppfCovering Xᵢ f]
      (D : AlgebraicGeometry.AlgebraicSpace.DescentData Xᵢ f),
      AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace
          (AlgebraicGeometry.AlgebraicSpace.DescentData.gluedSheaf Xᵢ f D).obj ↔
        D.IsEffective)
