module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Thickening.Deformation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry (Scheme)
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsThickening

variable {S : Scheme.{u}} {X X' Y Y' B B' : AlgebraicSpace S}
variable {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'}
variable {f : X ⟶ Y} {f' : X' ⟶ Y'}
variable {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
variable [thickeningX : IsThickening iX] [thickeningY : IsThickening iY]
variable [thickeningB : IsThickening iB] [finiteTypeY' : LocallyOfFiniteType pY']
variable [flatX' : Flat pX'] [finitePresentationX' : LocallyOfFinitePresentation pX']
variable (sq : CommSq f iX iY f')
variable (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
variable (pullbackX : IsPullback pX iX iB pX') (pullbackY : IsPullback pY iY iB pY')
variable (d : ℕ)

/- Lemma 76.18.5 (1): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is representable if and only if `f'` is representable. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.relativelyRepresentable_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (yoneda.relativelyRepresentable f ↔ yoneda.relativelyRepresentable f'))

/- Lemma 76.18.5 (2): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is flat if and only if `f'` is flat. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.flat_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (Flat f ↔ Flat f'))

/- Lemma 76.18.5 (3): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is an isomorphism if and only if `f'` is an isomorphism. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.isIso_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (IsIso f ↔ IsIso f'))

/- Lemma 76.18.5 (4): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is an open immersion if and only if `f'` is an open immersion. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.isOpenImmersion_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (IsOpenImmersion f ↔ IsOpenImmersion f'))

/- Lemma 76.18.5 (5): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is quasi-compact if and only if `f'` is quasi-compact. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.quasiCompact_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (QuasiCompact f ↔ QuasiCompact f'))

/- Lemma 76.18.5 (6): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is universally closed if and only if `f'` is universally closed. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.universallyClosed_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (UniversallyClosed f ↔ UniversallyClosed f'))

/- Lemma 76.18.5 (7): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is separated if and only if `f'` is separated. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.separated_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (Separated f ↔ Separated f'))

/- Lemma 76.18.5 (8): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is quasi-separated if and only if `f'` is quasi-separated. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.quasiSeparated_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (QuasiSeparated f ↔ QuasiSeparated f'))

/- Lemma 76.18.5 (9): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is a monomorphism if and only if `f'` is a monomorphism. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.mono_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (Mono f ↔ Mono f'))

/- Lemma 76.18.5 (10): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is surjective if and only if `f'` is surjective. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.surjective_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (Surjective f ↔ Surjective f'))

/- Lemma 76.18.5 (11): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is universally injective if and only if `f'` is universally injective. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.universallyInjective_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (UniversallyInjective f ↔ UniversallyInjective f'))

/- Lemma 76.18.5 (12): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is affine if and only if `f'` is affine. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.affine_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (Affine f ↔ Affine f'))

/- Lemma 76.18.5 (13): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is locally quasi-finite if and only if `f'` is locally quasi-finite. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.locallyQuasiFinite_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (LocallyQuasiFinite f ↔ LocallyQuasiFinite f'))

/- Lemma 76.18.5 (14): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is locally of finite type of relative dimension `d` if and only if
`f'` is locally of finite type of relative dimension `d`. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.relativeDimension_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    ∀ d : ℕ,
    (LocallyOfFiniteType f ∧ RelativeDimension f d) ↔
      (LocallyOfFiniteType f' ∧ RelativeDimension f' d))

/- Lemma 76.18.5 (15): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is universally open if and only if `f'` is universally open. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.universallyOpen_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (UniversallyOpen f ↔ UniversallyOpen f'))

/- Lemma 76.18.5 (16): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is syntomic if and only if `f'` is syntomic. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.syntomic_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (Syntomic f ↔ Syntomic f'))

/- Lemma 76.18.5 (17): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is smooth if and only if `f'` is smooth. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.smooth_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (Smooth f ↔ Smooth f'))

/- Lemma 76.18.5 (18): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is unramified if and only if `f'` is unramified. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.unramified_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (Unramified f ↔ Unramified f'))

/- Lemma 76.18.5 (19): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is étale if and only if `f'` is étale. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.etale_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (Etale f ↔ Etale f'))

/- Lemma 76.18.5 (20): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is proper if and only if `f'` is proper. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.proper_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (Proper f ↔ Proper f'))

/- Lemma 76.18.5 (21): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is finite if and only if `f'` is finite. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.isFinite_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (IsFinite f ↔ IsFinite f'))

/- Lemma 76.18.5 (22): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is finite locally free if and only if `f'` is finite locally free. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.finiteLocallyFree_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    (FiniteLocallyFree f ↔ FiniteLocallyFree f'))

/- Lemma 76.18.5 (23): in the stated cartesian diagram of thickenings of algebraic
spaces, `f` is finite locally free of rank `d` if and only if `f'` is finite
locally free of rank `d`. -/
@[stacks 0CGX]
#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.finiteLocallyFreeOfRank_iff :
    CommSq f iX iY f' →
    (f ≫ pY = pX) → (f' ≫ pY' = pX') →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    ∀ d : ℕ,
    FiniteLocallyFreeOfRank f d ↔ FiniteLocallyFreeOfRank f' d)

end AlgebraicGeometry.AlgebraicSpace.IsThickening
