/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap73.Definition_73_4_1_Precoverage
public import stacks_project.Chap74.Definition_74_21_1_EtaleSmoothLocal
public import stacks_project.Chap74.Lemma_74_10_2_BaseChange

/-!
# Characterizations of étale-smooth locality on source-and-target

A morphism property of algebraic spaces that is étale-smooth local on
source-and-target may be checked on a surjective-left mixed square, on every
étale comparison into a smooth base change, on a smooth target cover, on an
étale source cover, or on mixed smooth-target and étale-source covers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget

variable {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))

/-- A morphism has an étale-smooth-local-on-source-and-target property if and
only if the property holds on the top arrow of some commutative square with
smooth right vertical arrow, étale comparison into the fibre product, and
surjective left vertical arrow. -/
theorem iff_exists_surjective_square [IsEtaleSmoothLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P f ↔
      ∃ (U V : AlgebraicSpace S) (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V)
        (sq : CommSq h a b f),
          Smooth b ∧ Etale (etaleSmoothSquareLift sq) ∧ Surjective a ∧ P h :=
  sorry

/-- A morphism has an étale-smooth-local-on-source-and-target property if and
only if the top arrow of every commutative square with smooth right vertical
arrow and étale comparison `U ⟶ pullback f b` has the property. -/
theorem iff_forall_comparison [IsEtaleSmoothLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P f ↔
      ∀ {U V : AlgebraicSpace S} (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V)
        (sq : CommSq h a b f),
        Smooth b → Etale (etaleSmoothSquareLift sq) → P h :=
  sorry

/-- A morphism has an étale-smooth-local-on-source-and-target property if and
only if the property holds after base change along every member of some smooth
covering of the target. -/
theorem iff_exists_targetCover [IsEtaleSmoothLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P f ↔ ∃ 𝒰 : (smoothPrecoverage S).ZeroHypercover.{u} Y,
      ∀ i : 𝒰.I₀, P (pullback.snd f (𝒰.f i)) :=
  sorry

/-- A morphism has an étale-smooth-local-on-source-and-target property if and
only if every member of some étale covering of the source has the property after
composition with the morphism. -/
theorem iff_exists_sourceCover [IsEtaleSmoothLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P f ↔ ∃ 𝒰 : (@etalePrecoverage S).ZeroHypercover.{u} X,
      ∀ i : 𝒰.I₀, P (𝒰.f i ≫ f) :=
  sorry

/-- A morphism has an étale-smooth-local-on-source-and-target property if and
only if, after some smooth covering of the target, each base change admits an
étale source covering whose composites to the target-cover member have the
property. -/
theorem iff_exists_targetSourceCovers [IsEtaleSmoothLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P f ↔ ∃ 𝒰 : (smoothPrecoverage S).ZeroHypercover.{u} Y, ∀ i : 𝒰.I₀,
      ∃ 𝒱 : (@etalePrecoverage S).ZeroHypercover.{u} (pullback f (𝒰.f i)),
        ∀ j : 𝒱.I₀, P (𝒱.f j ≫ pullback.snd f (𝒰.f i)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget
