/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform.Etale
import StacksCheckRecall

/-!
# Étale localization and strict transform

Blowups and strict transforms of spaces and quasi-coherent modules commute
with étale scheme localization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.18.2 (Étale localization and strict transform)
Étale localization of blowups and the two induced comparison morphisms. -/
@[stacks 0863] #check (AlgebraicGeometry.AlgebraicSpace.strictTransform_etale_exists_isPullback :
    ∀ {S : Scheme.{u}} {B B' X V' : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) (f : X ⟶ B)
    {U V : Over S} (α : ofOver U ⟶ X) (β : ofOver V ⟶ B) (h : U ⟶ V)
    (v : V' ⟶ ofOver V)
    [IsBlowup b Z] [IsBlowup v (Z.inverseImageSubspace β)] [Etale α] [Etale β]
    (sq : CommSq α (ofOverMap h) f β),
    ∃ (g' : V' ⟶ B') (hg' : IsPullback g' v b β),
      Etale g' ∧ Etale (strictTransformAmbientMap b f α β h v g' sq.w hg'.w))

#check (AlgebraicGeometry.AlgebraicSpace.strictTransform_etale_isPullback :
    ∀ {S : Scheme.{u}} {B B' X V' : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) (f : X ⟶ B)
    {U V : Over S} (α : ofOver U ⟶ X) (β : ofOver V ⟶ B) (h : U ⟶ V)
    (v : V' ⟶ ofOver V)
    [IsBlowup b Z] [IsBlowup v (Z.inverseImageSubspace β)] [Etale α] [Etale β]
    [QuasiCompact
      (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι]
    [QuasiCompact
      (strictTransformOpenComplement v
        ((Z.inverseImageSubspace β).inverseImageSubspace v) (ofOverMap h)).ι]
    (sq : CommSq α (ofOverMap h) f β)
    (g' : V' ⟶ B') (hg' : IsPullback g' v b β),
    ∃ i :
      (strictTransform v ((Z.inverseImageSubspace β).inverseImageSubspace v)
          (ofOverMap h)).X ⟶
        (strictTransform b (Z.inverseImageSubspace b) f).X,
      IsPullback i
        ((strictTransform v ((Z.inverseImageSubspace β).inverseImageSubspace v)
            (ofOverMap h)).ι ≫ pullback.fst (ofOverMap h) v)
        ((strictTransform b (Z.inverseImageSubspace b) f).ι ≫ pullback.fst f b)
        α)

#check (AlgebraicGeometry.AlgebraicSpace.strictTransform_etale_inverseImage :
    ∀ {S : Scheme.{u}} {B B' X V' : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) (f : X ⟶ B)
    {U V : Over S} (α : ofOver U ⟶ X) (β : ofOver V ⟶ B) (h : U ⟶ V)
    (v : V' ⟶ ofOver V)
    [IsBlowup b Z] [IsBlowup v (Z.inverseImageSubspace β)] [Etale α] [Etale β]
    [QuasiCompact
      (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι]
    [QuasiCompact
      (strictTransformOpenComplement v
        ((Z.inverseImageSubspace β).inverseImageSubspace v) (ofOverMap h)).ι]
    (sq : CommSq α (ofOverMap h) f β)
    (g' : V' ⟶ B') (hg' : IsPullback g' v b β),
    ∃ i :
      (strictTransform v ((Z.inverseImageSubspace β).inverseImageSubspace v)
          (ofOverMap h)).X ⟶
        (strictTransform b (Z.inverseImageSubspace b) f).X,
      IsPullback i
        (strictTransform v ((Z.inverseImageSubspace β).inverseImageSubspace v)
          (ofOverMap h)).ι
        (strictTransform b (Z.inverseImageSubspace b) f).ι
        (strictTransformAmbientMap b f α β h v g' sq.w hg'.w))

#check (AlgebraicGeometry.AlgebraicSpace.strictTransformModule_etale_pullback :
    ∀ {S : Scheme.{u}} {B B' X V' : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) (f : X ⟶ B)
    {U V : Over S} (α : ofOver U ⟶ X) (β : ofOver V ⟶ B) (h : U ⟶ V)
    (v : V' ⟶ ofOver V)
    [IsBlowup b Z] [IsBlowup v (Z.inverseImageSubspace β)] [Etale α] [Etale β]
    (sq : CommSq α (ofOverMap h) f β)
    (g' : V' ⟶ B') (hg' : IsPullback g' v b β)
    (F : X.Modules) [F.IsQuasicoherent],
    ∃ e :
      (Modules.pullback (strictTransformAmbientMap b f α β h v g' sq.w hg'.w)).obj
          (strictTransformModule b (Z.inverseImageSubspace b) f F) ≅
        strictTransformModule v ((Z.inverseImageSubspace β).inverseImageSubspace v)
          (ofOverMap h) ((Modules.pullback α).obj F),
      (Modules.pullback (strictTransformAmbientMap b f α β h v g' sq.w hg'.w)).map
          (strictTransformπ b (Z.inverseImageSubspace b) f F) ≫ e.hom =
        strictTransformEtalePullbackπ Z b f α β h v g' sq.w hg'.w F)
