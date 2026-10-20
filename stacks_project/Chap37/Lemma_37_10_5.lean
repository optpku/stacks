/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.Deformation
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

variable {X X' Y Y' S S' : Scheme.{u}}
variable {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iS : S ⟶ S'}
variable {f : X ⟶ Y} {f' : X' ⟶ Y'}
variable {pX : X ⟶ S} {pX' : X' ⟶ S'} {pY : Y ⟶ S} {pY' : Y' ⟶ S'}
variable [thickeningX : IsThickening iX] [thickeningY : IsThickening iY]
variable [thickeningS : IsThickening iS] [finiteTypeY' : LocallyOfFiniteType pY']
variable [flatX' : Flat pX'] [finitePresentationX' : LocallyOfFinitePresentation pX']
variable (sq : CommSq f iX iY f')
variable (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
variable (pullbackX : IsPullback pX iX iS pX') (pullbackY : IsPullback pY iY iS pY')
variable (d : ℕ)

/- Lemma 37.10.5 (1): in the stated cartesian diagram of thickenings, `f` is flat if and
only if `f'` is flat. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.flat_iff sq triangle triangle' pullbackX pullbackY :
  Flat f ↔ Flat f')

/- Lemma 37.10.5 (2): in the stated cartesian diagram of thickenings, `f` is an
isomorphism if and only if `f'` is an isomorphism. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.isIso_iff sq triangle triangle' pullbackX pullbackY :
  IsIso f ↔ IsIso f')

/- Lemma 37.10.5 (3): in the stated cartesian diagram of thickenings, `f` is an open
immersion if and only if `f'` is an open immersion. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.isOpenImmersion_iff
  sq triangle triangle' pullbackX pullbackY : IsOpenImmersion f ↔ IsOpenImmersion f')

/- Lemma 37.10.5 (4): in the stated cartesian diagram of thickenings, `f` is quasi-compact
if and only if `f'` is quasi-compact. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.quasiCompact_iff
  sq triangle triangle' pullbackX pullbackY : QuasiCompact f ↔ QuasiCompact f')

/- Lemma 37.10.5 (5): in the stated cartesian diagram of thickenings, `f` is universally
closed if and only if `f'` is universally closed. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.universallyClosed_iff
  sq triangle triangle' pullbackX pullbackY : UniversallyClosed f ↔ UniversallyClosed f')

/- Lemma 37.10.5 (6): in the stated cartesian diagram of thickenings, `f` is separated if
and only if `f'` is separated. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.isSeparated_iff
  sq triangle triangle' pullbackX pullbackY : IsSeparated f ↔ IsSeparated f')

/- Lemma 37.10.5 (7): in the stated cartesian diagram of thickenings, `f` is
quasi-separated if and only if `f'` is quasi-separated. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.quasiSeparated_iff
  sq triangle triangle' pullbackX pullbackY : QuasiSeparated f ↔ QuasiSeparated f')

/- Lemma 37.10.5 (8): in the stated cartesian diagram of thickenings, `f` is a
monomorphism if and only if `f'` is a monomorphism. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.mono_iff sq triangle triangle' pullbackX pullbackY :
  Mono f ↔ Mono f')

/- Lemma 37.10.5 (9): in the stated cartesian diagram of thickenings, `f` is surjective if
and only if `f'` is surjective. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.surjective_iff
  sq triangle triangle' pullbackX pullbackY : Surjective f ↔ Surjective f')

/- Lemma 37.10.5 (10): in the stated cartesian diagram of thickenings, `f` is universally
injective if and only if `f'` is universally injective. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.universallyInjective_iff
  sq triangle triangle' pullbackX pullbackY : UniversallyInjective f ↔ UniversallyInjective f')

/- Lemma 37.10.5 (11): in the stated cartesian diagram of thickenings, `f` is affine if and
only if `f'` is affine. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.isAffineHom_iff
  sq triangle triangle' pullbackX pullbackY : IsAffineHom f ↔ IsAffineHom f')

/- Lemma 37.10.5 (12): in the stated cartesian diagram of thickenings, `f` is locally
quasi-finite if and only if `f'` is locally quasi-finite. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.locallyQuasiFinite_iff
  sq triangle triangle' pullbackX pullbackY : LocallyQuasiFinite f ↔ LocallyQuasiFinite f')

/- Lemma 37.10.5 (13): in the stated cartesian diagram of thickenings, `f` has relative
dimension `d` if and only if `f'` has relative dimension `d`. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.relativeDimension_iff
  sq triangle triangle' pullbackX pullbackY d :
    Scheme.Hom.RelativeDimension f d ↔ Scheme.Hom.RelativeDimension f' d)

/- Lemma 37.10.5 (14): in the stated cartesian diagram of thickenings, `f` is universally
open if and only if `f'` is universally open. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.universallyOpen_iff
  sq triangle triangle' pullbackX pullbackY : UniversallyOpen f ↔ UniversallyOpen f')

/- Lemma 37.10.5 (15): in the stated cartesian diagram of thickenings, `f` is syntomic if
and only if `f'` is syntomic. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.syntomic_iff sq triangle triangle' pullbackX pullbackY :
  Syntomic f ↔ Syntomic f')

/- Lemma 37.10.5 (16): in the stated cartesian diagram of thickenings, `f` is smooth if and
only if `f'` is smooth. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.smooth_iff sq triangle triangle' pullbackX pullbackY :
  Smooth f ↔ Smooth f')

/- Lemma 37.10.5 (17): in the stated cartesian diagram of thickenings, `f` is unramified if
and only if `f'` is unramified. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.unramified_iff
  sq triangle triangle' pullbackX pullbackY : Unramified f ↔ Unramified f')

/- Lemma 37.10.5 (18): in the stated cartesian diagram of thickenings, `f` is étale if and
only if `f'` is étale. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.etale_iff sq triangle triangle' pullbackX pullbackY :
  Etale f ↔ Etale f')

/- Lemma 37.10.5 (19): in the stated cartesian diagram of thickenings, `f` is proper if and
only if `f'` is proper. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.isProper_iff sq triangle triangle' pullbackX pullbackY :
  IsProper f ↔ IsProper f')

/- Lemma 37.10.5 (20): in the stated cartesian diagram of thickenings, `f` is finite if and
only if `f'` is finite. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.isFinite_iff sq triangle triangle' pullbackX pullbackY :
  IsFinite f ↔ IsFinite f')

/- Lemma 37.10.5 (21): in the stated cartesian diagram of thickenings, `f` is finite locally
free if and only if `f'` is finite locally free. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.isFiniteLocallyFree_iff
  sq triangle triangle' pullbackX pullbackY : IsFiniteLocallyFree f ↔ IsFiniteLocallyFree f')

/- Lemma 37.10.5 (22): in the stated cartesian diagram of thickenings, `f` is finite locally
free of rank `d` if and only if `f'` is finite locally free of rank `d`. -/
@[stacks 0CF4]
#check (AlgebraicGeometry.IsThickening.isFiniteLocallyFreeOfRank_iff
  sq triangle triangle' pullbackX pullbackY d :
    IsFiniteLocallyFreeOfRank f d ↔ IsFiniteLocallyFreeOfRank f' d)
