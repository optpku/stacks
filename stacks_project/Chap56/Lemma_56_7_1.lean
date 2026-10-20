/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.FunctorExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u w

/- Lemma 56.7.1 (1): a functor between coherent modules on Noetherian schemes extends
to quasicoherent modules, preserves filtered colimits, and is unique up to the unique natural
isomorphism compatible with its restriction to coherent modules. -/
@[stacks 0FZL] #check (AlgebraicGeometry.Scheme.coherentFunctor_existsUniqueFilteredColimitExtension :
    ∀ {X : Scheme.{u}} {Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace),
    ∃ (G : Scheme.QCoh X ⥤ Scheme.QCoh Y)
      (eG : Scheme.coherentToQCoh X ⋙ G ≅ F ⋙ Scheme.coherentToQCoh Y)
      (_ : PreservesFilteredColimits G),
      ∀ (H : Scheme.QCoh X ⥤ Scheme.QCoh Y)
        (eH : Scheme.coherentToQCoh X ⋙ H ≅ F ⋙ Scheme.coherentToQCoh Y),
        PreservesFilteredColimits H →
          ∃! α : G ≅ H,
            Functor.isoWhiskerLeft (Scheme.coherentToQCoh X) α ≪≫ eH = eG)

/- Lemma 56.7.1 (2): the filtered-colimit-preserving extension of an additive functor on
coherent modules preserves arbitrary direct sums. -/
@[stacks 0FZL] #check (AlgebraicGeometry.Scheme.coherentFunctorExtension_preservesCoproducts :
    ∀ {X : Scheme.{u}} {Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace)
    (G : Scheme.QCoh X ⥤ Scheme.QCoh Y) [PreservesFilteredColimits G]
    (eG : Scheme.coherentToQCoh X ⋙ G ≅ F ⋙ Scheme.coherentToQCoh Y)
    [F.Additive] (J : Type w),
    PreservesColimitsOfShape (Discrete J) G)

/- Lemma 56.7.1 (3): the filtered-colimit-preserving extension of an exact functor on
coherent modules is exact. -/
@[stacks 0FZL] #check (AlgebraicGeometry.Scheme.coherentFunctorExtension_exact :
    ∀ {X : Scheme.{u}} {Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace)
    (G : Scheme.QCoh X ⥤ Scheme.QCoh Y) [PreservesFilteredColimits G]
    (eG : Scheme.coherentToQCoh X ⋙ G ≅ F ⋙ Scheme.coherentToQCoh Y)
    (hF : exactFunctor (RingedSpace.Coh X.toRingedSpace)
      (RingedSpace.Coh Y.toRingedSpace) F),
    exactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) G)

/- Lemma 56.7.1 (4): the filtered-colimit-preserving extension of a left exact functor on
coherent modules is left exact. -/
@[stacks 0FZL] #check (AlgebraicGeometry.Scheme.coherentFunctorExtension_leftExact :
    ∀ {X : Scheme.{u}} {Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace)
    (G : Scheme.QCoh X ⥤ Scheme.QCoh Y) [PreservesFilteredColimits G]
    (eG : Scheme.coherentToQCoh X ⋙ G ≅ F ⋙ Scheme.coherentToQCoh Y)
    (hF : leftExactFunctor (RingedSpace.Coh X.toRingedSpace)
      (RingedSpace.Coh Y.toRingedSpace) F),
    leftExactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) G)

/- Lemma 56.7.1 (5): the filtered-colimit-preserving extension of a right exact functor on
coherent modules is right exact. -/
@[stacks 0FZL] #check (AlgebraicGeometry.Scheme.coherentFunctorExtension_rightExact :
    ∀ {X : Scheme.{u}} {Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace)
    (G : Scheme.QCoh X ⥤ Scheme.QCoh Y) [PreservesFilteredColimits G]
    (eG : Scheme.coherentToQCoh X ⋙ G ≅ F ⋙ Scheme.coherentToQCoh Y)
    (hF : rightExactFunctor (RingedSpace.Coh X.toRingedSpace)
      (RingedSpace.Coh Y.toRingedSpace) F),
    rightExactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) G)
