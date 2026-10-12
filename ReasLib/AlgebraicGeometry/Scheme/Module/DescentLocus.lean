/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A morphism `j : Z ⟶ S` represents the locus where the module `E` descends along
`f : X ⟶ S` if, after every base change `g : T ⟶ S`, factoring through `j` is
equivalent to the pullback of `E` being pulled back from a finite locally free module on `T`. -/
def RepresentsDescentLocus {X S Z : Scheme.{u}}
    (f : X ⟶ S) (E : X.Modules) (j : Z ⟶ S) : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ S),
    Nonempty (Over.mk g ⟶ Over.mk j) ↔
      ∃ (N : T.Modules) (_ : N.IsFiniteLocallyFree),
        Nonempty
          ((Scheme.Modules.pullback (pullback.snd f g)).obj N ≅
            (Scheme.Modules.pullback (pullback.fst f g)).obj E)

/-- The universal property characterizing a morphism that represents the descent locus. -/
theorem representsDescentLocus_iff {X S Z : Scheme.{u}}
    (f : X ⟶ S) (E : X.Modules) (j : Z ⟶ S) :
    RepresentsDescentLocus f E j ↔
      ∀ {T : Scheme.{u}} (g : T ⟶ S),
        Nonempty (Over.mk g ⟶ Over.mk j) ↔
          ∃ (N : T.Modules) (_ : N.IsFiniteLocallyFree),
            Nonempty
              ((Scheme.Modules.pullback (pullback.snd f g)).obj N ≅
                (Scheme.Modules.pullback (pullback.fst f g)).obj E) := sorry

/-- The locus where a finite locally free module descends along a flat proper finitely
presented morphism is represented by a finitely presented immersion, provided the
structure-sheaf unit is an isomorphism after every base change. -/
theorem existsDescentLocus {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (h_unit : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso (SheafOfModules.unitToPushforwardObjUnit
        (pullback.snd f g).toRingCatSheafHom)) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ S) (_ : IsImmersion j)
      (_ : Scheme.Hom.FinitePresentation j), RepresentsDescentLocus f E j := sorry

/-- A finite locally free module whose restrictions to all fibers are finite free
descends along a flat proper finitely presented morphism to a reduced base, provided
the structure-sheaf unit is an isomorphism after every base change. -/
theorem existsPullbackOfFiniteFreeFibers {X S : Scheme.{u}} [IsReduced S]
    (f : X ⟶ S) [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (h_unit : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso (SheafOfModules.unitToPushforwardObjUnit
        (pullback.snd f g).toRingCatSheafHom))
    (h_fiber : ∀ s : S,
      SheafOfModules.IsFiniteFree
        ((Scheme.Modules.pullback (f.fiberι s)).obj E)) :
    ∃ (N : S.Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Scheme.Modules.pullback f).obj N ≅ E) := sorry

end AlgebraicGeometry.Scheme.Modules
