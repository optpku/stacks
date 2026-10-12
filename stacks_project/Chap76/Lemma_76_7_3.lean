/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap76.Definition_76_7_2_Differentials

/-!
# Restriction of the sheaf of differentials of a morphism of algebraic spaces

Along an étale-vertical commutative square, the sheaf of relative differentials of
`f : X ⟶ Y` restricts on the small étale site of `U` to the sheaf of relative
differentials of `ψ : U ⟶ V`. When `U` and `V` are schemes, this agrees with the
usual Zariski sheaf of differentials of `U ⟶ V`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Lemma 76.7.3 (1): For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` and a
commutative square with étale vertical arrows `a : U ⟶ X` and `b : V ⟶ Y`,
`Modules.restrict (relativeDifferentials f) a` is isomorphic to `relativeDifferentials ψ`. -/
@[stacks 04CU]
theorem restrict_relativeDifferentials
    {S : Scheme.{u}} {X Y U V : AlgebraicSpace S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : U ⟶ X) (b : V ⟶ Y)
    [Etale a] [Etale b] (sq : CommSq a ψ f b) :
    IsIsomorphic (Modules.restrict (relativeDifferentials f) a) (relativeDifferentials ψ) :=
  sorry

/-- Lemma 76.7.3 (2): If `U` and `V` are schemes, the restricted sheaf of differentials agrees
with `RingedSpace.Hom.differentials` of the morphism of schemes `U ⟶ V`. -/
@[stacks 04CU]
theorem restrict_relativeDifferentials_ofOver
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {U V : Over S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    [Etale a] [Etale b] (sq : CommSq a (ofOverMap ψ) f b) :
    IsIsomorphic
      ((Modules.restrictToScheme U).obj (Modules.restrict (relativeDifferentials f) a))
      (RingedSpace.Hom.differentials ψ.left.toShHom) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
