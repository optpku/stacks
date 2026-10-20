/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Thickening.FiniteOrderDeformation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Properties
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FiniteOrderProperties
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry (Scheme)
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening

variable {S : Scheme.{u}} {X X' Y Y' B B' : AlgebraicSpace S}
variable {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'}
variable {f : X ⟶ Y} {f' : X' ⟶ Y'}
variable {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
variable [thickeningX : IsThickening iX] [thickeningY : IsThickening iY]
variable [finiteOrderB : IsFiniteOrderThickening iB] [flatX' : Flat pX']
variable (sq : CommSq f iX iY f')
variable (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
variable (pullbackX : IsPullback pX iX iB pX') (pullbackY : IsPullback pY iY iB pY')
variable (d : ℕ)

/- The generalized transfer statements below apply to the original diagram by
bundling `iX` and `iY` with `Thickening.of` and bundling `f` and `f'` with
`Thickening.homMk` using `sq.w`. Pullback cancellation (`IsPullback.of_right`)
applied to the two base pullback squares and the commuting triangles gives
`IsPullback f iX iY f'`, whose flip is `IsPullback iX f f' iY`, the orientation
used for a bundled morphism of thickenings. Finite order of `iX` follows by
base change from `iB`. Thus the generalized checks introduce no additional
hypotheses on the original diagram. -/

/- Lemma 76.18.3 (1): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is representable if and only if `f'` is representable. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.relativelyRepresentable_iff :
    ∀ {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U),
      yoneda.relativelyRepresentable g.left ↔ yoneda.relativelyRepresentable g.right)

/- Lemma 76.18.3 (2): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is flat if and only if `f'` is flat. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.flat_iff
  sq triangle triangle' pullbackX pullbackY : Flat f ↔ Flat f')

/- Lemma 76.18.3 (3): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is an isomorphism if and only if `f'` is an isomorphism. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.isIso_iff
  sq triangle triangle' pullbackX pullbackY : IsIso f ↔ IsIso f')

/- Lemma 76.18.3 (4): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is an open immersion if and only if `f'` is an open
immersion. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.isOpenImmersion_iff
  sq triangle triangle' pullbackX pullbackY : IsOpenImmersion f ↔ IsOpenImmersion f')

/- Lemma 76.18.3 (5): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is quasi-compact if and only if `f'` is quasi-compact. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.quasiCompact_iff :
    ∀ {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U),
      QuasiCompact g.left ↔ QuasiCompact g.right)

/- Lemma 76.18.3 (6): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is universally closed if and only if `f'` is universally
closed. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.universallyClosed_iff :
    ∀ {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U),
      UniversallyClosed g.left ↔ UniversallyClosed g.right)

/- Lemma 76.18.3 (7): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is separated if and only if `f'` is separated. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.separated_iff :
    ∀ {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U),
      Separated g.left ↔ Separated g.right)

/- Lemma 76.18.3 (7): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is quasi-separated if and only if `f'` is quasi-separated. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.quasiSeparated_iff :
    ∀ {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U),
      QuasiSeparated g.left ↔ QuasiSeparated g.right)

/- Lemma 76.18.3 (8): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is a monomorphism if and only if `f'` is a monomorphism. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.mono_iff_of_isPullback :
    ∀ {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
      (cartesian : IsPullback T.hom g.left g.right U.hom)
      [IsFiniteOrderThickening T.hom],
      Mono g.left ↔ Mono g.right)

/- Lemma 76.18.3 (9): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is surjective if and only if `f'` is surjective. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.surjective_iff :
    ∀ {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U),
      Surjective g.left ↔ Surjective g.right)

/- Lemma 76.18.3 (10): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is universally injective if and only if `f'` is
universally injective. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.universallyInjective_iff :
    ∀ {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U),
      UniversallyInjective g.left ↔ UniversallyInjective g.right)

/- Lemma 76.18.3 (11): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is affine if and only if `f'` is affine. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.affine_iff :
    ∀ {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U),
      Affine g.left ↔ Affine g.right)

/- Lemma 76.18.3 (12): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is locally of finite type if and only if `f'` is locally
of finite type. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.locallyOfFiniteType_iff_of_isPullback :
    ∀ {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
      (cartesian : IsPullback T.hom g.left g.right U.hom)
      [IsFiniteOrderThickening T.hom],
      LocallyOfFiniteType g.left ↔ LocallyOfFiniteType g.right)

/- Lemma 76.18.3 (13): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is locally quasi-finite if and only if `f'` is locally
quasi-finite. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.locallyQuasiFinite_iff_of_isPullback :
    ∀ {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
      (cartesian : IsPullback T.hom g.left g.right U.hom)
      [IsFiniteOrderThickening T.hom],
      LocallyQuasiFinite g.left ↔ LocallyQuasiFinite g.right)

/- Lemma 76.18.3 (14): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is locally of finite presentation if and only if `f'` is
locally of finite presentation. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.locallyOfFinitePresentation_iff
  sq triangle triangle' pullbackX pullbackY :
    LocallyOfFinitePresentation f ↔ LocallyOfFinitePresentation f')

/- Lemma 76.18.3 (15): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is locally of finite type of relative dimension `d` if
and only if `f'` is locally of finite type of relative dimension `d`. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.relativeDimension_iff_of_isPullback :
    ∀ {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
      (cartesian : IsPullback T.hom g.left g.right U.hom)
      [IsFiniteOrderThickening T.hom] (d : ℕ),
      (LocallyOfFiniteType g.left ∧ RelativeDimension g.left d) ↔
        (LocallyOfFiniteType g.right ∧ RelativeDimension g.right d))

/- Lemma 76.18.3 (16): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is universally open if and only if `f'` is universally
open. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.universallyOpen_iff :
    ∀ {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U),
      UniversallyOpen g.left ↔ UniversallyOpen g.right)

/- Lemma 76.18.3 (17): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is syntomic if and only if `f'` is syntomic. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.syntomic_iff
  sq triangle triangle' pullbackX pullbackY : Syntomic f ↔ Syntomic f')

/- Lemma 76.18.3 (18): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is smooth if and only if `f'` is smooth. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.smooth_iff
  sq triangle triangle' pullbackX pullbackY : Smooth f ↔ Smooth f')

/- Lemma 76.18.3 (19): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is unramified if and only if `f'` is unramified. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.unramified_iff_of_isPullback :
    ∀ {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
      (cartesian : IsPullback T.hom g.left g.right U.hom)
      [IsFiniteOrderThickening T.hom],
      Unramified g.left ↔ Unramified g.right)

/- Lemma 76.18.3 (20): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is étale if and only if `f'` is étale. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.etale_iff
  sq triangle triangle' pullbackX pullbackY : Etale f ↔ Etale f')

/- Lemma 76.18.3 (21): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is proper if and only if `f'` is proper. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.proper_iff_of_isPullback :
    ∀ {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
      (cartesian : IsPullback T.hom g.left g.right U.hom)
      [IsFiniteOrderThickening T.hom],
      Proper g.left ↔ Proper g.right)

/- Lemma 76.18.3 (22): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is integral if and only if `f'` is integral. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.isIntegralHom_iff :
    ∀ {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U),
      IsIntegralHom g.left ↔ IsIntegralHom g.right)

/- Lemma 76.18.3 (23): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is finite if and only if `f'` is finite. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.isFinite_iff_of_isPullback :
    ∀ {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
      (cartesian : IsPullback T.hom g.left g.right U.hom)
      [IsFiniteOrderThickening T.hom],
      IsFinite g.left ↔ IsFinite g.right)

/- Lemma 76.18.3 (24): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is finite locally free if and only if `f'` is finite
locally free. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.finiteLocallyFree_iff
  sq triangle triangle' pullbackX pullbackY :
    FiniteLocallyFree f ↔ FiniteLocallyFree f')

/- Lemma 76.18.3 (24): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is finite locally free of rank `d` if and only if `f'`
is finite locally free of rank `d`. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.finiteLocallyFreeOfRank_iff
  sq triangle triangle' pullbackX pullbackY d :
    FiniteLocallyFreeOfRank f d ↔ FiniteLocallyFreeOfRank f' d)

end AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening
