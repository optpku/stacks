/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import ReasLib.Algebra.Module.Flat.Relative
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_31_1
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver

/-!
# Transitivity and converse criteria for relative flatness of modules

Pointwise relative flatness of a quasi-coherent module on an algebraic space is transitive
along a morphism that is flat at the image point. Conversely, flatness of the base at that
image can be recovered from relative flatness over both the intermediate and final targets
when a field-valued pullback is nonzero, or from faithful flatness of an étale stalk.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u v w

namespace Module

/-- Faithful flatness of an `A`-module after restricting scalars along `f : R →+* A`. -/
def FaithfullyFlatAlong {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (f : R →+* A) (M : Type w) [AddCommGroup M] [Module A M] : Prop :=
  @Module.FaithfullyFlat R M _ _ (Module.compHom M f)

/-- Unfolding lemma for faithful flatness after restriction of scalars. -/
theorem faithfullyFlatAlong_iff {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (f : R →+* A) (M : Type w) [AddCommGroup M] [Module A M] :
    FaithfullyFlatAlong f M ↔ @Module.FaithfullyFlat R M _ _ (Module.compHom M f) :=
  sorry

end Module

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}

/-- Lemma 67.31.4 (1): Let `S` be a scheme. Let `X ⟶ Y ⟶ Z` be morphisms of algebraic spaces
over `S`. Let `F` be a quasi-coherent sheaf on `X`. Let `x ∈ |X|` with image `y ∈ |Y|`. If `F`
is flat at `x` over `Y` and `Y` is flat at `y` over `Z`, then `F` is flat at `x` over `Z`. -/
@[stacks 05VX]
theorem flatOverAt_trans (F : X.Modules) [F.IsQuasicoherent] (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Points X) (hF : flatOverAt F f x) (hY : FlatAt g (Points.map f x)) :
    flatOverAt F (f ≫ g) x :=
  sorry

/-- Lemma 67.31.4 (2): Let `x : Spec(K) ⟶ X` be a representative of `x`. If `F` is flat at `x`
over `Y`, the pullback `x^* F` is nonzero, and `F` is flat at `x` over `Z`, then `Y` is flat at
`y` over `Z`. -/
@[stacks 05VX]
theorem flatAt_of_flatOverAt_of_pullback_ne_zero (F : X.Modules) [F.IsQuasicoherent]
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Points X) (p : FieldValuedPoint X) (hp : Points.mk p = x)
    (hXY : flatOverAt F f x) (hne : ¬ IsZero ((pullback p.hom).obj F))
    (hXZ : flatOverAt F (f ≫ g) x) :
    FlatAt g (Points.map f x) :=
  sorry

/-- Lemma 67.31.4 (3): Let `x̄` be a geometric point of `X` lying over `x` with image `ȳ` in
`Y`. If the étale stalk `F_x̄` is a faithfully flat `𝒪_{Y, ȳ}`-module and `F` is flat at `x`
over `Z`, then `Y` is flat at `y` over `Z`. -/
@[stacks 05VX]
theorem flatAt_of_stalk_faithfullyFlatAlong (F : X.Modules) [F.IsQuasicoherent]
    (f : X ⟶ Y) (g : Y ⟶ Z) (xbar : GeometricPoint X) (x : Points X) (hx : xbar.liesOver x)
    (hff : Module.FaithfullyFlatAlong (etaleLocalRingMap f xbar) (stalkModuleCat xbar F))
    (hXZ : flatOverAt F (f ≫ g) x) :
    FlatAt g (Points.map f x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
