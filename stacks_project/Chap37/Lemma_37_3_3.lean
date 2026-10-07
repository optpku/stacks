module

public import ReasLib.AlgebraicGeometry.Morphisms.Thickening.FiniteOrder
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 37.3.3 (1): in a cartesian morphism to a finite-order thickening, the closed
and ambient maps are simultaneously closed immersions. -/
@[stacks 09ZW] #check
  (AlgebraicGeometry.Thickening.Hom.isClosedImmersion_iff_of_isPullback :
    ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U)
      (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.IsFiniteOrderThickening U.hom],
      AlgebraicGeometry.IsClosedImmersion g.left ↔
        AlgebraicGeometry.IsClosedImmersion g.right)

/- Lemma 37.3.3 (2): in a cartesian morphism to a finite-order thickening, the closed
and ambient maps are simultaneously locally of finite type. -/
@[stacks 09ZW] #check
  (AlgebraicGeometry.Thickening.Hom.locallyOfFiniteType_iff_of_isPullback :
    ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U)
      (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.IsFiniteOrderThickening U.hom],
      AlgebraicGeometry.LocallyOfFiniteType g.left ↔
        AlgebraicGeometry.LocallyOfFiniteType g.right)

/- Lemma 37.3.3 (3): in a cartesian morphism to a finite-order thickening, the closed
and ambient maps are simultaneously locally quasi-finite. -/
@[stacks 09ZW] #check
  (AlgebraicGeometry.Thickening.Hom.locallyQuasiFinite_iff_of_isPullback :
    ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U)
      (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.IsFiniteOrderThickening U.hom],
      AlgebraicGeometry.LocallyQuasiFinite g.left ↔
        AlgebraicGeometry.LocallyQuasiFinite g.right)

/- Lemma 37.3.3 (4): in a cartesian morphism to a finite-order thickening, the closed
and ambient maps have relative dimension `d` simultaneously. -/
@[stacks 09ZW] #check
  (AlgebraicGeometry.Thickening.Hom.relativeDimension_iff_of_isPullback :
    ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U)
      (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.IsFiniteOrderThickening U.hom] (d : ℕ),
      AlgebraicGeometry.Scheme.Hom.RelativeDimension g.left d ↔
        AlgebraicGeometry.Scheme.Hom.RelativeDimension g.right d)

/- Lemma 37.3.3 (5): in a cartesian morphism to a finite-order thickening, the relative
differential sheaves of the closed and ambient maps vanish simultaneously. -/
@[stacks 09ZW] #check
  (AlgebraicGeometry.Thickening.Hom.isZero_relativeDifferentials_iff_of_isPullback :
    ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U)
      (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.IsFiniteOrderThickening U.hom],
      IsZero (Ω[g.left.toShHom]) ↔ IsZero (Ω[g.right.toShHom]))

/- Lemma 37.3.3 (6): in a cartesian morphism to a finite-order thickening, the closed
and ambient maps are simultaneously unramified. -/
@[stacks 09ZW] #check
  (AlgebraicGeometry.Thickening.Hom.unramified_iff_of_isPullback :
    ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U)
      (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.IsFiniteOrderThickening U.hom],
      AlgebraicGeometry.Unramified g.left ↔ AlgebraicGeometry.Unramified g.right)

/- Lemma 37.3.3 (7): in a cartesian morphism to a finite-order thickening, the closed
and ambient maps are simultaneously proper. -/
@[stacks 09ZW] #check
  (AlgebraicGeometry.Thickening.Hom.isProper_iff_of_isPullback :
    ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U)
      (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.IsFiniteOrderThickening U.hom],
      AlgebraicGeometry.IsProper g.left ↔ AlgebraicGeometry.IsProper g.right)

/- Lemma 37.3.3 (8): in a cartesian morphism to a finite-order thickening, the closed
and ambient maps are simultaneously finite. -/
@[stacks 09ZW] #check
  (AlgebraicGeometry.Thickening.Hom.isFinite_iff_of_isPullback :
    ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U)
      (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.IsFiniteOrderThickening U.hom],
      AlgebraicGeometry.IsFinite g.left ↔ AlgebraicGeometry.IsFinite g.right)

/- Lemma 37.3.3 (9): in a cartesian morphism to a finite-order thickening, the closed
and ambient maps are simultaneously monomorphisms. -/
@[stacks 09ZW] #check
  (AlgebraicGeometry.Thickening.Hom.mono_iff_of_isPullback :
    ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U)
      (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.IsFiniteOrderThickening U.hom],
      Mono g.left ↔ Mono g.right)

/- Lemma 37.3.3 (10): in a cartesian morphism to a finite-order thickening, the closed
and ambient maps are simultaneously immersions. -/
@[stacks 09ZW] #check
  (AlgebraicGeometry.Thickening.Hom.isImmersion_iff_of_isPullback :
    ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U)
      (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.IsFiniteOrderThickening U.hom],
      AlgebraicGeometry.IsImmersion g.left ↔ AlgebraicGeometry.IsImmersion g.right)
