/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.VectorBundleLocus
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Rigidified
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RigidifiedPicard

variable {k : Type u} [Field k]
variable (X : SchemeOverField k)
variable (σ : Spec (CommRingCat.of k) ⟶ X.left)
variable (hσ : σ ≫ X.hom = 𝟙 _)

/-- A rigidified Picard class lies in the pushforward-line locus when its chosen invertible
representative has derived pushforward a rank-one vector bundle in degree `0`. -/
def IsPushforwardLine (T : Over (Spec (CommRingCat.of k)))
    (x : (functor X σ hσ).obj (op T)) : Prop :=
  Scheme.ModuleDerived.IsVectorBundleOfRankInDegree
    ((RingedSpace.moduleDerivedPushforward (pullback.snd X.hom T.hom).toShHom).obj
      ((DerivedCategory.singleFunctor (pullback X.hom T.hom).Modules 0).obj
        (Scheme.PicardGroup.repr x.1))) 0 1

/-- Membership in `IsPushforwardLine` is the rank-one, degree-zero derived-pushforward
condition. -/
theorem isPushforwardLine_iff (T : Over (Spec (CommRingCat.of k)))
    (x : (functor X σ hσ).obj (op T)) :
    IsPushforwardLine X σ hσ T x ↔
      Scheme.ModuleDerived.IsVectorBundleOfRankInDegree
        ((RingedSpace.moduleDerivedPushforward (pullback.snd X.hom T.hom).toShHom).obj
          ((DerivedCategory.singleFunctor (pullback X.hom T.hom).Modules 0).obj
            (Scheme.PicardGroup.repr x.1))) 0 1 := sorry

/-- The pushforward-line condition may be tested on any invertible module representing the
underlying Picard class. -/
theorem isPushforwardLine_iff_of_picardClass (T : Over (Spec (CommRingCat.of k)))
    (x : (functor X σ hσ).obj (op T)) (ℒ : (pullback X.hom T.hom).Modules)
    [MonoidalCategory.isInvertibleObject ℒ]
    (hℒ : Scheme.Modules.picardClass ℒ = x.1) :
    IsPushforwardLine X σ hσ T x ↔
      Scheme.ModuleDerived.IsVectorBundleOfRankInDegree
        ((RingedSpace.moduleDerivedPushforward (pullback.snd X.hom T.hom).toShHom).obj
          ((DerivedCategory.singleFunctor (pullback X.hom T.hom).Modules 0).obj ℒ)) 0 1 := sorry

/-- The rank-one, degree-zero derived-pushforward condition is preserved by base change. -/
theorem IsPushforwardLine.map [Curve X] [Smooth X.hom] [Projective X.hom]
    {T T' : Over (Spec (CommRingCat.of k))} (g : T' ⟶ T)
    {x : (functor X σ hσ).obj (op T)} (hx : IsPushforwardLine X σ hσ T x) :
    IsPushforwardLine X σ hσ T' (map X σ hσ g x) := sorry

/-- The subfunctor of the rigidified Picard functor cut out by a rank-one derived pushforward
concentrated in degree `0`. -/
def pushforwardLineSubfunctor [Curve X] [Smooth X.hom] [Projective X.hom] :
    CategoryTheory.Subfunctor (functor X σ hσ) where
  obj T := setOf (IsPushforwardLine X σ hσ T.unop)
  map g x hx := hx.map X σ hσ g.unop

/-- Membership in the pushforward-line subfunctor is exactly the rank-one, degree-zero
derived-pushforward condition. -/
theorem mem_pushforwardLineSubfunctor [Curve X] [Smooth X.hom] [Projective X.hom]
    (T : Over (Spec (CommRingCat.of k))) (x : (functor X σ hσ).obj (op T)) :
    x ∈ (pushforwardLineSubfunctor X σ hσ).obj (op T) ↔
      IsPushforwardLine X σ hσ T x := sorry

/-- The inclusion of the pushforward-line subfunctor is relatively representable by open
immersions. -/
theorem pushforwardLineSubfunctor_isOpen
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom]
    (σ : Spec (CommRingCat.of k) ⟶ X.left) (hσ : σ ≫ X.hom = 𝟙 _) :
    (MorphismProperty.over (@IsOpenImmersion)).relative uliftYoneda.{u + 1}
      (pushforwardLineSubfunctor X σ hσ).ι := sorry

end AlgebraicGeometry.RigidifiedPicard
