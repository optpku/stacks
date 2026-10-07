module

public import stacks_project.Chap76.Lemma_76_18_3_Deformation
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

/- Lemma 76.18.3 (1): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is representable if and only if `f'` is representable. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.relativelyRepresentable_iff
  sq triangle triangle' pullbackX pullbackY :
    yoneda.relativelyRepresentable f ↔ yoneda.relativelyRepresentable f')

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
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.quasiCompact_iff
  sq triangle triangle' pullbackX pullbackY : QuasiCompact f ↔ QuasiCompact f')

/- Lemma 76.18.3 (6): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is universally closed if and only if `f'` is universally
closed. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.universallyClosed_iff
  sq triangle triangle' pullbackX pullbackY :
    UniversallyClosed f ↔ UniversallyClosed f')

/- Lemma 76.18.3 (7): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is separated if and only if `f'` is separated. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.separated_iff
  sq triangle triangle' pullbackX pullbackY : Separated f ↔ Separated f')

/- Lemma 76.18.3 (8): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is quasi-separated if and only if `f'` is quasi-separated. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.quasiSeparated_iff
  sq triangle triangle' pullbackX pullbackY : QuasiSeparated f ↔ QuasiSeparated f')

/- Lemma 76.18.3 (9): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is a monomorphism if and only if `f'` is a monomorphism. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.mono_iff
  sq triangle triangle' pullbackX pullbackY : Mono f ↔ Mono f')

/- Lemma 76.18.3 (10): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is surjective if and only if `f'` is surjective. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.surjective_iff
  sq triangle triangle' pullbackX pullbackY : Surjective f ↔ Surjective f')

/- Lemma 76.18.3 (11): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is universally injective if and only if `f'` is
universally injective. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.universallyInjective_iff
  sq triangle triangle' pullbackX pullbackY :
    UniversallyInjective f ↔ UniversallyInjective f')

/- Lemma 76.18.3 (12): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is affine if and only if `f'` is affine. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.affine_iff
  sq triangle triangle' pullbackX pullbackY : Affine f ↔ Affine f')

/- Lemma 76.18.3 (13): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is locally of finite type if and only if `f'` is locally
of finite type. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.locallyOfFiniteType_iff
  sq triangle triangle' pullbackX pullbackY :
    LocallyOfFiniteType f ↔ LocallyOfFiniteType f')

/- Lemma 76.18.3 (14): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is locally quasi-finite if and only if `f'` is locally
quasi-finite. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.locallyQuasiFinite_iff
  sq triangle triangle' pullbackX pullbackY :
    LocallyQuasiFinite f ↔ LocallyQuasiFinite f')

/- Lemma 76.18.3 (15): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is locally of finite presentation if and only if `f'` is
locally of finite presentation. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.locallyOfFinitePresentation_iff
  sq triangle triangle' pullbackX pullbackY :
    LocallyOfFinitePresentation f ↔ LocallyOfFinitePresentation f')

/- Lemma 76.18.3 (16): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is locally of finite type of relative dimension `d` if
and only if `f'` is locally of finite type of relative dimension `d`. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.relativeDimension_iff
  sq triangle triangle' pullbackX pullbackY d :
    (LocallyOfFiniteType f ∧ RelativeDimension f d) ↔
      (LocallyOfFiniteType f' ∧ RelativeDimension f' d))

/- Lemma 76.18.3 (17): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is universally open if and only if `f'` is universally
open. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.universallyOpen_iff
  sq triangle triangle' pullbackX pullbackY : UniversallyOpen f ↔ UniversallyOpen f')

/- Lemma 76.18.3 (18): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is syntomic if and only if `f'` is syntomic. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.syntomic_iff
  sq triangle triangle' pullbackX pullbackY : Syntomic f ↔ Syntomic f')

/- Lemma 76.18.3 (19): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is smooth if and only if `f'` is smooth. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.smooth_iff
  sq triangle triangle' pullbackX pullbackY : Smooth f ↔ Smooth f')

/- Lemma 76.18.3 (20): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is unramified if and only if `f'` is unramified. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.unramified_iff
  sq triangle triangle' pullbackX pullbackY : Unramified f ↔ Unramified f')

/- Lemma 76.18.3 (21): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is étale if and only if `f'` is étale. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.etale_iff
  sq triangle triangle' pullbackX pullbackY : Etale f ↔ Etale f')

/- Lemma 76.18.3 (22): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is proper if and only if `f'` is proper. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.proper_iff
  sq triangle triangle' pullbackX pullbackY : Proper f ↔ Proper f')

/- Lemma 76.18.3 (23): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is integral if and only if `f'` is integral. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.isIntegralHom_iff
  sq triangle triangle' pullbackX pullbackY : IsIntegralHom f ↔ IsIntegralHom f')

/- Lemma 76.18.3 (24): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is finite if and only if `f'` is finite. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.isFinite_iff
  sq triangle triangle' pullbackX pullbackY : IsFinite f ↔ IsFinite f')

/- Lemma 76.18.3 (25): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is finite locally free if and only if `f'` is finite
locally free. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.finiteLocallyFree_iff
  sq triangle triangle' pullbackX pullbackY :
    FiniteLocallyFree f ↔ FiniteLocallyFree f')

/- Lemma 76.18.3 (26): in the stated cartesian diagram of finite-order thickenings
of algebraic spaces, `f` is finite locally free of rank `d` if and only if `f'`
is finite locally free of rank `d`. -/
@[stacks 0CG6]
#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.finiteLocallyFreeOfRank_iff
  sq triangle triangle' pullbackX pullbackY d :
    FiniteLocallyFreeOfRank f d ↔ FiniteLocallyFreeOfRank f' d)

end AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening
