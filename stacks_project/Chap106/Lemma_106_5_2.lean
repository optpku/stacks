module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening.Deformation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Syntomic
import StacksCheckRecall

/-!
# Deformation of morphism properties of algebraic stacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open CategoryTheory.FiberedCategoryOver.Groupoids
open CategoryTheory.Bicategory
open scoped Bicategory

universe u

/- Lemma 106.5.2 (1): in a 2-commutative triangle of thickenings of algebraic
stacks, with Y' ⟶ B' locally of finite type, X' ⟶ B' flat and locally of finite
presentation, and both vertical squares 2-fibre products, f is flat if and only
if f' is flat. -/
@[stacks 0CJC] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.flat_iff :
  ∀ {S : Scheme.{u}} {X X' Y Y' B B' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [AlgebraicStack B] [AlgebraicStack B']
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [AlgebraicStack.IsThickening iX] [AlgebraicStack.IsThickening iY]
    [AlgebraicStack.IsThickening iB] [LocallyOfFiniteType pY']
    [Flat pX'] [LocallyOfFinitePresentation pX']
    (sq : AlgebraicStack.IsThickening.Hom iX iY f f')
    (hX : AlgebraicStack.IsThickening.Hom iX iB pX pX')
    (hY : AlgebraicStack.IsThickening.Hom iY iB pY pY')
    (triangle : f ≫ pY ≅ pX) (triangle' : f' ≫ pY' ≅ pX')
    (pullbackX : PseudoPullbackCone.IsBilimit
      (⟨X, pX, iX, hX.w⟩ : PseudoPullbackCone iB pX'))
    (pullbackY : PseudoPullbackCone.IsBilimit
      (⟨Y, pY, iY, hY.w⟩ : PseudoPullbackCone iB pY')),
    Flat f ↔ Flat f')

/- Lemma 106.5.2 (2): under the same hypotheses, f is an isomorphism if and only
if f' is an isomorphism. -/
@[stacks 0CJC] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.isIso_iff :
  ∀ {S : Scheme.{u}} {X X' Y Y' B B' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [AlgebraicStack B] [AlgebraicStack B']
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [AlgebraicStack.IsThickening iX] [AlgebraicStack.IsThickening iY]
    [AlgebraicStack.IsThickening iB] [LocallyOfFiniteType pY']
    [Flat pX'] [LocallyOfFinitePresentation pX']
    (sq : AlgebraicStack.IsThickening.Hom iX iY f f')
    (hX : AlgebraicStack.IsThickening.Hom iX iB pX pX')
    (hY : AlgebraicStack.IsThickening.Hom iY iB pY pY')
    (triangle : f ≫ pY ≅ pX) (triangle' : f' ≫ pY' ≅ pX')
    (pullbackX : PseudoPullbackCone.IsBilimit
      (⟨X, pX, iX, hX.w⟩ : PseudoPullbackCone iB pX'))
    (pullbackY : PseudoPullbackCone.IsBilimit
      (⟨Y, pY, iY, hY.w⟩ : PseudoPullbackCone iB pY')),
    (toBasedFunctor f).IsEquivalence ↔ (toBasedFunctor f').IsEquivalence)

/- Lemma 106.5.2 (3): under the same hypotheses, f is an open immersion if and
only if f' is an open immersion. -/
@[stacks 0CJC] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.openImmersion_iff :
  ∀ {S : Scheme.{u}} {X X' Y Y' B B' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [AlgebraicStack B] [AlgebraicStack B']
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [AlgebraicStack.IsThickening iX] [AlgebraicStack.IsThickening iY]
    [AlgebraicStack.IsThickening iB] [LocallyOfFiniteType pY']
    [Flat pX'] [LocallyOfFinitePresentation pX']
    (sq : AlgebraicStack.IsThickening.Hom iX iY f f')
    (hX : AlgebraicStack.IsThickening.Hom iX iB pX pX')
    (hY : AlgebraicStack.IsThickening.Hom iY iB pY pY')
    (triangle : f ≫ pY ≅ pX) (triangle' : f' ≫ pY' ≅ pX')
    (pullbackX : PseudoPullbackCone.IsBilimit
      (⟨X, pX, iX, hX.w⟩ : PseudoPullbackCone iB pX'))
    (pullbackY : PseudoPullbackCone.IsBilimit
      (⟨Y, pY, iY, hY.w⟩ : PseudoPullbackCone iB pY')),
    Groupoids.Hom.OpenImmersion f ↔ Groupoids.Hom.OpenImmersion f')

/- Lemma 106.5.2 (4): under the same hypotheses, f is a monomorphism if and only
if f' is a monomorphism. -/
@[stacks 0CJC] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.mono_iff :
  ∀ {S : Scheme.{u}} {X X' Y Y' B B' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [AlgebraicStack B] [AlgebraicStack B']
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [AlgebraicStack.IsThickening iX] [AlgebraicStack.IsThickening iY]
    [AlgebraicStack.IsThickening iB] [LocallyOfFiniteType pY']
    [Flat pX'] [LocallyOfFinitePresentation pX']
    (sq : AlgebraicStack.IsThickening.Hom iX iY f f')
    (hX : AlgebraicStack.IsThickening.Hom iX iB pX pX')
    (hY : AlgebraicStack.IsThickening.Hom iY iB pY pY')
    (triangle : f ≫ pY ≅ pX) (triangle' : f' ≫ pY' ≅ pX')
    (pullbackX : PseudoPullbackCone.IsBilimit
      (⟨X, pX, iX, hX.w⟩ : PseudoPullbackCone iB pX'))
    (pullbackY : PseudoPullbackCone.IsBilimit
      (⟨Y, pY, iY, hY.w⟩ : PseudoPullbackCone iB pY')),
    Groupoids.Hom.Mono f ↔ Groupoids.Hom.Mono f')

/- Lemma 106.5.2 (5): under the same hypotheses, f is locally quasi-finite if and
only if f' is locally quasi-finite. -/
@[stacks 0CJC] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.locallyQuasiFinite_iff :
  ∀ {S : Scheme.{u}} {X X' Y Y' B B' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [AlgebraicStack B] [AlgebraicStack B']
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [AlgebraicStack.IsThickening iX] [AlgebraicStack.IsThickening iY]
    [AlgebraicStack.IsThickening iB] [LocallyOfFiniteType pY']
    [Flat pX'] [LocallyOfFinitePresentation pX']
    (sq : AlgebraicStack.IsThickening.Hom iX iY f f')
    (hX : AlgebraicStack.IsThickening.Hom iX iB pX pX')
    (hY : AlgebraicStack.IsThickening.Hom iY iB pY pY')
    (triangle : f ≫ pY ≅ pX) (triangle' : f' ≫ pY' ≅ pX')
    (pullbackX : PseudoPullbackCone.IsBilimit
      (⟨X, pX, iX, hX.w⟩ : PseudoPullbackCone iB pX'))
    (pullbackY : PseudoPullbackCone.IsBilimit
      (⟨Y, pY, iY, hY.w⟩ : PseudoPullbackCone iB pY')),
    LocallyQuasiFinite f ↔ LocallyQuasiFinite f')

/- Lemma 106.5.2 (6): under the same hypotheses, f is syntomic if and only if f'
is syntomic. -/
@[stacks 0CJC] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.syntomic_iff :
  ∀ {S : Scheme.{u}} {X X' Y Y' B B' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [AlgebraicStack B] [AlgebraicStack B']
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [AlgebraicStack.IsThickening iX] [AlgebraicStack.IsThickening iY]
    [AlgebraicStack.IsThickening iB] [LocallyOfFiniteType pY']
    [Flat pX'] [LocallyOfFinitePresentation pX']
    (sq : AlgebraicStack.IsThickening.Hom iX iY f f')
    (hX : AlgebraicStack.IsThickening.Hom iX iB pX pX')
    (hY : AlgebraicStack.IsThickening.Hom iY iB pY pY')
    (triangle : f ≫ pY ≅ pX) (triangle' : f' ≫ pY' ≅ pX')
    (pullbackX : PseudoPullbackCone.IsBilimit
      (⟨X, pX, iX, hX.w⟩ : PseudoPullbackCone iB pX'))
    (pullbackY : PseudoPullbackCone.IsBilimit
      (⟨Y, pY, iY, hY.w⟩ : PseudoPullbackCone iB pY')),
    Syntomic f ↔ Syntomic f')

/- Lemma 106.5.2 (7): under the same hypotheses, f is smooth if and only if f' is
smooth. -/
@[stacks 0CJC] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.smooth_iff :
  ∀ {S : Scheme.{u}} {X X' Y Y' B B' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [AlgebraicStack B] [AlgebraicStack B']
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [AlgebraicStack.IsThickening iX] [AlgebraicStack.IsThickening iY]
    [AlgebraicStack.IsThickening iB] [LocallyOfFiniteType pY']
    [Flat pX'] [LocallyOfFinitePresentation pX']
    (sq : AlgebraicStack.IsThickening.Hom iX iY f f')
    (hX : AlgebraicStack.IsThickening.Hom iX iB pX pX')
    (hY : AlgebraicStack.IsThickening.Hom iY iB pY pY')
    (triangle : f ≫ pY ≅ pX) (triangle' : f' ≫ pY' ≅ pX')
    (pullbackX : PseudoPullbackCone.IsBilimit
      (⟨X, pX, iX, hX.w⟩ : PseudoPullbackCone iB pX'))
    (pullbackY : PseudoPullbackCone.IsBilimit
      (⟨Y, pY, iY, hY.w⟩ : PseudoPullbackCone iB pY')),
    Smooth f ↔ Smooth f')

/- Lemma 106.5.2 (8): under the same hypotheses, f is unramified if and only if
f' is unramified. -/
@[stacks 0CJC] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.unramified_iff :
  ∀ {S : Scheme.{u}} {X X' Y Y' B B' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [AlgebraicStack B] [AlgebraicStack B']
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [AlgebraicStack.IsThickening iX] [AlgebraicStack.IsThickening iY]
    [AlgebraicStack.IsThickening iB] [LocallyOfFiniteType pY']
    [Flat pX'] [LocallyOfFinitePresentation pX']
    (sq : AlgebraicStack.IsThickening.Hom iX iY f f')
    (hX : AlgebraicStack.IsThickening.Hom iX iB pX pX')
    (hY : AlgebraicStack.IsThickening.Hom iY iB pY pY')
    (triangle : f ≫ pY ≅ pX) (triangle' : f' ≫ pY' ≅ pX')
    (pullbackX : PseudoPullbackCone.IsBilimit
      (⟨X, pX, iX, hX.w⟩ : PseudoPullbackCone iB pX'))
    (pullbackY : PseudoPullbackCone.IsBilimit
      (⟨Y, pY, iY, hY.w⟩ : PseudoPullbackCone iB pY')),
    Unramified f ↔ Unramified f')

/- Lemma 106.5.2 (9): under the same hypotheses, f is étale if and only if f' is
étale. -/
@[stacks 0CJC] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.etale_iff :
  ∀ {S : Scheme.{u}} {X X' Y Y' B B' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [AlgebraicStack B] [AlgebraicStack B']
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [AlgebraicStack.IsThickening iX] [AlgebraicStack.IsThickening iY]
    [AlgebraicStack.IsThickening iB] [LocallyOfFiniteType pY']
    [Flat pX'] [LocallyOfFinitePresentation pX']
    (sq : AlgebraicStack.IsThickening.Hom iX iY f f')
    (hX : AlgebraicStack.IsThickening.Hom iX iB pX pX')
    (hY : AlgebraicStack.IsThickening.Hom iY iB pY pY')
    (triangle : f ≫ pY ≅ pX) (triangle' : f' ≫ pY' ≅ pX')
    (pullbackX : PseudoPullbackCone.IsBilimit
      (⟨X, pX, iX, hX.w⟩ : PseudoPullbackCone iB pX'))
    (pullbackY : PseudoPullbackCone.IsBilimit
      (⟨Y, pY, iY, hY.w⟩ : PseudoPullbackCone iB pY')),
    Etale f ↔ Etale f')

/- Lemma 106.5.2 (10): under the same hypotheses, f is finite if and only if f'
is finite. -/
@[stacks 0CJC] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.isFinite_iff :
  ∀ {S : Scheme.{u}} {X X' Y Y' B B' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [AlgebraicStack B] [AlgebraicStack B']
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [AlgebraicStack.IsThickening iX] [AlgebraicStack.IsThickening iY]
    [AlgebraicStack.IsThickening iB] [LocallyOfFiniteType pY']
    [Flat pX'] [LocallyOfFinitePresentation pX']
    (sq : AlgebraicStack.IsThickening.Hom iX iY f f')
    (hX : AlgebraicStack.IsThickening.Hom iX iB pX pX')
    (hY : AlgebraicStack.IsThickening.Hom iY iB pY pY')
    (triangle : f ≫ pY ≅ pX) (triangle' : f' ≫ pY' ≅ pX')
    (pullbackX : PseudoPullbackCone.IsBilimit
      (⟨X, pX, iX, hX.w⟩ : PseudoPullbackCone iB pX'))
    (pullbackY : PseudoPullbackCone.IsBilimit
      (⟨Y, pY, iY, hY.w⟩ : PseudoPullbackCone iB pY')),
    IsFinite f ↔ IsFinite f')
