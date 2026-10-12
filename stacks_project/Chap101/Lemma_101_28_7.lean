/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap78.Lemma_78_27_2_TrivialAction
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap101.Definition_101_28_1_Gerbe
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap101.Lemma_101_25_5_Surjective
public import stacks_project.Chap101.Lemma_101_33_7_ToBase
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

/-!
# Local classifying presentations of gerbes of algebraic stacks

A morphism of algebraic stacks is a gerbe over its target if and only if,
after an fppf cover of the target by an algebraic space, it becomes the
classifying stack of a flat, locally finitely presented group algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicStack
open GroupoidAlgebraicSpace GroupAlgebraicSpace TwoFibreProduct
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The source of `p : X ⟶ U.toGroupoids` is equivalent over `U` to the
classifying stack of the trivial action of `G`. -/
def IsTrivialActionQuotientOver {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} (p : X ⟶ U.toGroupoids)
    (G : GroupAlgebraicSpace U) : Prop :=
  ∃ e : X ≌ (ofAction G (trivialAction G)).quotientStack,
    Nonempty
      (e.hom ≫ GroupoidAlgebraicSpace.toBase (ofAction G (trivialAction G)) ≅ p)

namespace IsTrivialActionQuotientOver

/-- `IsTrivialActionQuotientOver p G` means there is an equivalence
`X ≌ (ofAction G (trivialAction G)).quotientStack` whose first 1-morphism
identifies `p` with the structure morphism of the classifying stack. -/
theorem iff {S : Scheme.{u}} {U : AlgebraicSpace S} {X : GroupoidsOver S}
    (p : X ⟶ U.toGroupoids) (G : GroupAlgebraicSpace U) :
    IsTrivialActionQuotientOver p G ↔
      ∃ e : X ≌ (ofAction G (trivialAction G)).quotientStack,
        Nonempty
          (e.hom ≫
              GroupoidAlgebraicSpace.toBase (ofAction G (trivialAction G)) ≅
            p) :=
  sorry

/-- An equivalence of the source of `p` with `[U / G]` over `U` witnesses
`IsTrivialActionQuotientOver p G`. -/
theorem of {S : Scheme.{u}} {U : AlgebraicSpace S} {X : GroupoidsOver S}
    {p : X ⟶ U.toGroupoids} {G : GroupAlgebraicSpace U}
    (e : X ≌ (ofAction G (trivialAction G)).quotientStack)
    (h : Nonempty
      (e.hom ≫ GroupoidAlgebraicSpace.toBase (ofAction G (trivialAction G)) ≅
        p)) :
    IsTrivialActionQuotientOver p G :=
  sorry

/-- `IsTrivialActionQuotientOver p G` supplies an equivalence of the source of
`p` with `[U / G]` over `U`. -/
theorem spec {S : Scheme.{u}} {U : AlgebraicSpace S} {X : GroupoidsOver S}
    {p : X ⟶ U.toGroupoids} {G : GroupAlgebraicSpace U}
    (h : IsTrivialActionQuotientOver p G) :
    ∃ e : X ≌ (ofAction G (trivialAction G)).quotientStack,
      Nonempty
        (e.hom ≫ GroupoidAlgebraicSpace.toBase (ofAction G (trivialAction G)) ≅
          p) :=
  sorry

end IsTrivialActionQuotientOver

namespace Gerbe

/-- Lemma 101.28.7: a morphism `π : X ⟶ Y` of algebraic stacks makes `X` a
gerbe over `Y` if and only if there exist an algebraic space `U`, a group
algebraic space `G` flat and locally of finite presentation over `U`, and a
surjective, flat, locally of finite presentation morphism
`g : U.toGroupoids ⟶ Y` such that
`TwoFibreProduct.apex π g` is equivalent to
`(ofAction G (trivialAction G)).quotientStack` over `U`. -/
@[stacks 06QH]
theorem iff_exists_trivialQuotient {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (π : X ⟶ Y) :
    Gerbe π ↔
      ∃ (U : AlgebraicSpace S) (G : GroupAlgebraicSpace U)
        (g : U.toGroupoids ⟶ Y),
        AlgebraicSpace.Flat G.X.hom ∧
          AlgebraicSpace.LocallyOfFinitePresentation G.X.hom ∧
          Surjective g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧
            IsTrivialActionQuotientOver
              (TwoFibreProduct.snd.{u + 1, u, u + 1, u} π g) G :=
  sorry

/-- A gerbe morphism of algebraic stacks admits an fppf algebraic-space cover
of the target after which it becomes the classifying stack of a flat, locally
finitely presented group algebraic space. -/
theorem exists_trivialQuotient {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (π : X ⟶ Y) [Gerbe π] :
    ∃ (U : AlgebraicSpace S) (G : GroupAlgebraicSpace U)
      (g : U.toGroupoids ⟶ Y),
      AlgebraicSpace.Flat G.X.hom ∧
        AlgebraicSpace.LocallyOfFinitePresentation G.X.hom ∧
        Surjective g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧
          IsTrivialActionQuotientOver
            (TwoFibreProduct.snd.{u + 1, u, u + 1, u} π g) G :=
  sorry

/-- If after an fppf algebraic-space cover of the target a morphism of
algebraic stacks becomes the classifying stack of a flat, locally finitely
presented group algebraic space, then it is a gerbe over the target. -/
theorem of_exists_trivialQuotient {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (π : X ⟶ Y)
    {U : AlgebraicSpace S} (G : GroupAlgebraicSpace U)
    (g : U.toGroupoids ⟶ Y) [AlgebraicSpace.Flat G.X.hom]
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom]
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    (h : IsTrivialActionQuotientOver
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} π g) G) :
    Gerbe π :=
  sorry

end Gerbe

end AlgebraicGeometry.AlgebraicStack
