/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback

/-!
# Composition of strict transforms

Direct and successive strict transforms are compared by their canonical quotient
maps and their inclusions into the common fibre-product ambient space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The composite of the two strict-transform quotient maps, transported to the
common ambient fibre product and transposed along its canonical pasting isomorphism. -/
def iteratedStrictTransformπ
    {S : Scheme.{u}} {B B' B'' X : AlgebraicSpace S}
    (b : B' ⟶ B) (b' : B'' ⟶ B')
    (E : ClosedSubspace B') (E' : ClosedSubspace B'')
    (f : X ⟶ B) (F : X.Modules) :
    (Modules.pullback (pullback.fst f (b' ≫ b))).obj F ⟶
      (Modules.pushforward (pullbackLeftPullbackSndIso f b b').hom).obj
        (strictTransformModule b' E' (pullback.snd f b)
          (strictTransformModule b E f F)) := by
  let c := pullbackLeftPullbackSndIso f b b'
  let r := pullback.fst f (b' ≫ b)
  let r1 := pullback.fst f b
  let r2 := pullback.fst (pullback.snd f b) b'
  have h : c.hom ≫ r = r2 ≫ r1 :=
    pullbackLeftPullbackSndIso_hom_fst f b b'
  let t : (Modules.pullback c.hom).obj ((Modules.pullback r).obj F) ⟶
      (Modules.pullback r2).obj ((Modules.pullback r1).obj F) :=
    (Modules.pullbackCompIso c.hom r).hom.app F ≫
      eqToHom (congrArg (fun q ↦ (Modules.pullback q).obj F) h) ≫
      (Modules.pullbackCompIso r2 r1).inv.app F
  exact (Modules.pullbackPushforwardAdjunction c.hom).homEquiv _ _
    (t ≫ (Modules.pullback r2).map (strictTransformπ b E f F) ≫
      strictTransformπ b' E' (pullback.snd f b) (strictTransformModule b E f F))

/-- The canonical morphism from a successive strict transform into the fibre product
of the original space with the twice-transformed base. -/
def iteratedStrictTransformι
    {S : Scheme.{u}} {B B' B'' X : AlgebraicSpace S}
    (b : B' ⟶ B) (b' : B'' ⟶ B')
    (E : ClosedSubspace B') (E' : ClosedSubspace B'') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι]
    [QuasiCompact
      (strictTransformOpenComplement b' E' (strictTransformSnd b E f)).ι] :
    (strictTransform b' E' (strictTransformSnd b E f)).X ⟶
      pullback f (b' ≫ b) :=
  pullback.lift
    (strictTransformFst b' E' (strictTransformSnd b E f) ≫ strictTransformFst b E f)
    (strictTransformSnd b' E' (strictTransformSnd b E f))
    (by
      rw [Category.assoc, strictTransform_condition b E f, ← Category.assoc,
        strictTransform_condition b' E' (strictTransformSnd b E f), Category.assoc])

/-- If two successive blowups compose to the blowup in a center supported on the
union of the first center and the image of the second, direct and successive strict
transforms of a quasi-coherent module agree compatibly with their quotient maps. -/
@[stacks 0868]
theorem strictTransformModule_isomorphic_pushforward_iteratedStrictTransform
    {S : Scheme.{u}} {B B' B'' X : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z]
    (Z' : ClosedSubspace B') (b' : B'' ⟶ B') [IsBlowup b' Z']
    (Y : ClosedSubspace B)
    (hY : Y.pointsSet = Z.pointsSet ∪ Points.map b '' Z'.pointsSet)
    [IsBlowup (b' ≫ b) Y]
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    ∃ e :
      strictTransformModule (b' ≫ b) (Y.inverseImageSubspace (b' ≫ b)) f F ≅
      (Modules.pushforward (pullbackLeftPullbackSndIso f b b').hom).obj
        (strictTransformModule b' (Z'.inverseImageSubspace b') (pullback.snd f b)
          (strictTransformModule b (Z.inverseImageSubspace b) f F)),
      strictTransformπ (b' ≫ b) (Y.inverseImageSubspace (b' ≫ b)) f F ≫ e.hom =
        iteratedStrictTransformπ b b' (Z.inverseImageSubspace b)
          (Z'.inverseImageSubspace b') f F :=
  sorry

/-- If two successive blowups compose to the blowup in a center supported on the
union of the first center and the image of the second, direct and successive strict
transforms agree as subspaces of their common fibre product. -/
@[stacks 0868]
theorem strictTransform_isomorphic_iteratedStrictTransform
    {S : Scheme.{u}} {B B' B'' X : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z]
    (Z' : ClosedSubspace B') (b' : B'' ⟶ B') [IsBlowup b' Z']
    (Y : ClosedSubspace B)
    (hY : Y.pointsSet = Z.pointsSet ∪ Points.map b '' Z'.pointsSet)
    [IsBlowup (b' ≫ b) Y]
    (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι]
    [QuasiCompact
      (strictTransformOpenComplement b' (Z'.inverseImageSubspace b')
        (strictTransformSnd b (Z.inverseImageSubspace b) f)).ι]
    [QuasiCompact
      (strictTransformOpenComplement (b' ≫ b) (Y.inverseImageSubspace (b' ≫ b)) f).ι] :
    ∃ e :
      (strictTransform (b' ≫ b) (Y.inverseImageSubspace (b' ≫ b)) f).X ≅
      (strictTransform b' (Z'.inverseImageSubspace b')
        (strictTransformSnd b (Z.inverseImageSubspace b) f)).X,
      e.hom ≫ iteratedStrictTransformι b b' (Z.inverseImageSubspace b)
        (Z'.inverseImageSubspace b') f =
          (strictTransform (b' ≫ b) (Y.inverseImageSubspace (b' ≫ b)) f).ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
