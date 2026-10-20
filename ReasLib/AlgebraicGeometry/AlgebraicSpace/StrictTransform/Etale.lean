/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback

/-!
# Étale localization of strict transforms

Blowups and strict transforms of algebraic spaces and quasi-coherent modules
commute with étale scheme localization. Module comparisons respect the
canonical quotient maps defining the strict transforms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B B' X V' : AlgebraicSpace S}
variable (Z : ClosedSubspace B) (b : B' ⟶ B) (f : X ⟶ B)
variable {U V : Over S} (α : ofOver U ⟶ X) (β : ofOver V ⟶ B) (h : U ⟶ V)
variable (v : V' ⟶ ofOver V)

/-- Two commutative squares induce a comparison between their fibre products. -/
def strictTransformAmbientMap (g' : V' ⟶ B')
    (wα : α ≫ f = ofOverMap h ≫ β) (wg' : g' ≫ b = v ≫ β) :
    pullback (ofOverMap h) v ⟶ pullback f b :=
  pullback.map (ofOverMap h) v f b α g' β wα.symm wg'.symm

/-- The fibre-product comparison projects to the given morphism on the first factor. -/
theorem strictTransformAmbientMap_fst (g' : V' ⟶ B')
    (wα : α ≫ f = ofOverMap h ≫ β) (wg' : g' ≫ b = v ≫ β) :
    strictTransformAmbientMap b f α β h v g' wα wg' ≫ pullback.fst f b =
      pullback.fst (ofOverMap h) v ≫ α := by
  exact pullback.lift_fst _ _ _

/-- The fibre-product comparison projects to the given morphism on the second factor. -/
theorem strictTransformAmbientMap_snd (g' : V' ⟶ B')
    (wα : α ≫ f = ofOverMap h ≫ β) (wg' : g' ≫ b = v ≫ β) :
    strictTransformAmbientMap b f α β h v g' wα wg' ≫ pullback.snd f b =
      pullback.snd (ofOverMap h) v ≫ g' := by
  exact pullback.lift_snd _ _ _

/-- Blowups in a closed subspace and its étale inverse image form a cartesian
square with étale comparison maps, also after adjoining a compatible étale scheme chart. -/
theorem strictTransform_etale_exists_isPullback
    [IsBlowup b Z] [IsBlowup v (Z.inverseImageSubspace β)] [Etale α] [Etale β]
    (sq : CommSq α (ofOverMap h) f β) :
    ∃ (g' : V' ⟶ B') (hg' : IsPullback g' v b β),
      Etale g' ∧ Etale (strictTransformAmbientMap b f α β h v g' sq.w hg'.w) :=
  sorry

/-- The local strict-transform quotient map, transported from the pullback of the
global ambient module through the fibre-product comparison and pullback composition. -/
def strictTransformEtalePullbackπ (g' : V' ⟶ B')
    (wα : α ≫ f = ofOverMap h ≫ β) (wg' : g' ≫ b = v ≫ β) (F : X.Modules) :
    (Modules.pullback (strictTransformAmbientMap b f α β h v g' wα wg')).obj
        ((strictTransformPullbackFunctor b f).obj F) ⟶
      strictTransformModule v ((Z.inverseImageSubspace β).inverseImageSubspace v)
        (ofOverMap h) ((Modules.pullback α).obj F) :=
  (Modules.pullbackCompIso (strictTransformAmbientMap b f α β h v g' wα wg')
      (pullback.fst f b)).hom.app F ≫
    eqToHom (congrArg (fun q ↦ (Modules.pullback q).obj F)
      (strictTransformAmbientMap_fst b f α β h v g' wα wg')) ≫
    (Modules.pullbackCompIso (pullback.fst (ofOverMap h) v) α).inv.app F ≫
    strictTransformπ v ((Z.inverseImageSubspace β).inverseImageSubspace v)
      (ofOverMap h) ((Modules.pullback α).obj F)

/-- Étale localization identifies the strict transforms of a quasi-coherent module
compatibly with their canonical quotient maps. -/
theorem strictTransformModule_etale_pullback
    [IsBlowup b Z] [IsBlowup v (Z.inverseImageSubspace β)] [Etale α] [Etale β]
    (sq : CommSq α (ofOverMap h) f β)
    (g' : V' ⟶ B') (hg' : IsPullback g' v b β)
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ e :
      (Modules.pullback (strictTransformAmbientMap b f α β h v g' sq.w hg'.w)).obj
          (strictTransformModule b (Z.inverseImageSubspace b) f F) ≅
        strictTransformModule v ((Z.inverseImageSubspace β).inverseImageSubspace v)
          (ofOverMap h) ((Modules.pullback α).obj F),
      (Modules.pullback (strictTransformAmbientMap b f α β h v g' sq.w hg'.w)).map
          (strictTransformπ b (Z.inverseImageSubspace b) f F) ≫ e.hom =
        strictTransformEtalePullbackπ Z b f α β h v g' sq.w hg'.w F :=
  sorry

/-- The localized strict transform is the inverse image of the global strict
transform in the ambient fibre product. -/
theorem strictTransform_etale_inverseImage
    [IsBlowup b Z] [IsBlowup v (Z.inverseImageSubspace β)] [Etale α] [Etale β]
    [QuasiCompact
      (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι]
    [QuasiCompact
      (strictTransformOpenComplement v
        ((Z.inverseImageSubspace β).inverseImageSubspace v) (ofOverMap h)).ι]
    (sq : CommSq α (ofOverMap h) f β)
    (g' : V' ⟶ B') (hg' : IsPullback g' v b β) :
    ∃ i :
      (strictTransform v ((Z.inverseImageSubspace β).inverseImageSubspace v)
          (ofOverMap h)).X ⟶
        (strictTransform b (Z.inverseImageSubspace b) f).X,
      IsPullback i
        (strictTransform v ((Z.inverseImageSubspace β).inverseImageSubspace v)
          (ofOverMap h)).ι
        (strictTransform b (Z.inverseImageSubspace b) f).ι
        (strictTransformAmbientMap b f α β h v g' sq.w hg'.w) :=
  sorry

/-- The strict transform of an étale scheme chart is cartesian over the global
strict transform and the original chart. -/
theorem strictTransform_etale_isPullback
    [IsBlowup b Z] [IsBlowup v (Z.inverseImageSubspace β)] [Etale α] [Etale β]
    [QuasiCompact
      (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι]
    [QuasiCompact
      (strictTransformOpenComplement v
        ((Z.inverseImageSubspace β).inverseImageSubspace v) (ofOverMap h)).ι]
    (sq : CommSq α (ofOverMap h) f β)
    (g' : V' ⟶ B') (hg' : IsPullback g' v b β) :
    ∃ i :
      (strictTransform v ((Z.inverseImageSubspace β).inverseImageSubspace v)
          (ofOverMap h)).X ⟶
        (strictTransform b (Z.inverseImageSubspace b) f).X,
      IsPullback i
        ((strictTransform v ((Z.inverseImageSubspace β).inverseImageSubspace v)
            (ofOverMap h)).ι ≫ pullback.fst (ofOverMap h) v)
        ((strictTransform b (Z.inverseImageSubspace b) f).ι ≫ pullback.fst f b)
        α :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
