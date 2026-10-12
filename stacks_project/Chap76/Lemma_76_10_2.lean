/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_10_2_FiniteOrder
import StacksCheckRecall

open CategoryTheory Limits
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.10.2 (1): in a cartesian morphism to a finite-order thickening, the closed
and ambient maps are simultaneously closed immersions. -/
@[stacks 09ZZ] #check
  (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.isClosedImmersion_iff_of_isPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
      (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening U.hom],
      AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion g.left ↔
        AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion g.right)

/- Lemma 76.10.2 (2): in a cartesian morphism to a finite-order thickening, the closed
and ambient maps are simultaneously locally of finite type. -/
@[stacks 09ZZ] #check
  (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.locallyOfFiniteType_iff_of_isPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
      (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening U.hom],
      AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.left ↔
        AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.right)

/- Lemma 76.10.2 (3): in a cartesian morphism to a finite-order thickening, the closed
and ambient maps are simultaneously locally quasi-finite. -/
@[stacks 09ZZ] #check
  (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.locallyQuasiFinite_iff_of_isPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
      (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening U.hom],
      AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite g.left ↔
        AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite g.right)

/- Lemma 76.10.2 (4): in a cartesian morphism to a finite-order thickening, the closed
and ambient maps are simultaneously locally of finite type of relative dimension `d`. -/
@[stacks 09ZZ] #check
  (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.relativeDimension_iff_of_isPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
      (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening U.hom] (d : ℕ),
      AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.left ∧
          AlgebraicGeometry.AlgebraicSpace.RelativeDimension g.left d ↔
        AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.right ∧
          AlgebraicGeometry.AlgebraicSpace.RelativeDimension g.right d)

/- Lemma 76.10.2 (5): in a cartesian morphism to a finite-order thickening, the relative
differential sheaves of the closed and ambient maps vanish simultaneously. -/
@[stacks 09ZZ] #check
  (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.isZero_relativeDifferentials_iff_of_isPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
      (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening U.hom],
      IsZero (Ω[g.left]) ↔ IsZero (Ω[g.right]))

/- Lemma 76.10.2 (6): in a cartesian morphism to a finite-order thickening, the closed
and ambient maps are simultaneously unramified. -/
@[stacks 09ZZ] #check
  (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.unramified_iff_of_isPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
      (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening U.hom],
      AlgebraicGeometry.AlgebraicSpace.Unramified g.left ↔
        AlgebraicGeometry.AlgebraicSpace.Unramified g.right)

/- Lemma 76.10.2 (7): in a cartesian morphism to a finite-order thickening, the closed
and ambient maps are simultaneously proper. -/
@[stacks 09ZZ] #check
  (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.proper_iff_of_isPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
      (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening U.hom],
      AlgebraicGeometry.AlgebraicSpace.Proper g.left ↔
        AlgebraicGeometry.AlgebraicSpace.Proper g.right)

/- Lemma 76.10.2 (8): in a cartesian morphism to a finite-order thickening, the closed
and ambient maps are simultaneously finite. -/
@[stacks 09ZZ] #check
  (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.isFinite_iff_of_isPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
      (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening U.hom],
      AlgebraicGeometry.AlgebraicSpace.IsFinite g.left ↔
        AlgebraicGeometry.AlgebraicSpace.IsFinite g.right)

/- Lemma 76.10.2 (9): in a cartesian morphism to a finite-order thickening, the closed
and ambient maps are simultaneously monomorphisms. -/
@[stacks 09ZZ] #check
  (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.mono_iff_of_isPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
      (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening U.hom],
      Mono g.left ↔ Mono g.right)

/- Lemma 76.10.2 (10): in a cartesian morphism to a finite-order thickening, the closed
and ambient maps are simultaneously immersions. -/
@[stacks 09ZZ] #check
  (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.isImmersion_iff_of_isPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
      (g : T ⟶ U) (sq : IsPullback T.hom g.left g.right U.hom)
      [AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening U.hom],
      AlgebraicGeometry.AlgebraicSpace.IsImmersion g.left ↔
        AlgebraicGeometry.AlgebraicSpace.IsImmersion g.right)
