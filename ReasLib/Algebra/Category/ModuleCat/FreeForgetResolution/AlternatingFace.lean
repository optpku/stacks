/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FreeForgetResolution.Contraction
public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.AlternatingFace.ModuleCat

/-!
@stack 0G5T

# Alternating-face complexes of free-forgetful resolutions

This leaf owns the alternating-face chain complex and its canonical quasi-isomorphic augmentation.
The underlying simplicial contraction used by the criterion lives in `Contraction`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SimplicialObject
open AlgebraicTopology

universe u

namespace CategoryTheory.ModuleCat.FreeForgetResolution

variable (R : Type u) [Ring R]

/-- The alternating-face chain complex of the free-forgetful resolution, functorial in the
resolved module. -/
@[stacks 0G5T "free-forgetful resolution chain-complex functor"]
noncomputable abbrev complex : ModuleCat.{u} R ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  evaluation R ⋙
    (SimplicialObject.Augmented.drop ⋙ alternatingFaceMapComplex (ModuleCat.{u} R))

/-- The canonical natural augmentation from the free-forgetful resolution complex to the
resolved module concentrated in degree zero. -/
@[stacks 0G5T "free-forgetful resolution chain-complex augmentation"]
noncomputable def augmentation :
    complex R ⟶ evaluation R ⋙
      (SimplicialObject.Augmented.point ⋙ ChainComplex.single₀ (ModuleCat.{u} R)) :=
  Functor.whiskerLeft (evaluation R) AlternatingFaceMapComplex.ε

/-- The component of the canonical chain-complex augmentation at a module `M`. -/
@[simp, stacks 0G5T "free-forgetful resolution augmentation component"]
theorem augmentation.app (M : ModuleCat R) :
    (augmentation R).app M =
      AlternatingFaceMapComplex.ε.app ((evaluation R).obj M) := sorry

/-- The canonical free-forgetful augmentation is pointwise a quasi-isomorphism as a natural
transformation of chain-complex-valued functors. -/
@[stacks 0G5T "free-forgetful augmentation in the pointwise quasi-isomorphism property"]
theorem augmentation.mem_quasiIso :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R)
      (ComplexShape.down ℕ)).functorCategory (ModuleCat.{u} R) (augmentation R) := sorry

/-- Every component of the canonical free-forgetful chain-complex augmentation is a
quasi-isomorphism. -/
@[stacks 0G5T "free-forgetful resolution alternating-face quasi-isomorphism"]
instance augmentation.quasiIso (M : ModuleCat R) :
    QuasiIso ((augmentation R).app M) := sorry

end CategoryTheory.ModuleCat.FreeForgetResolution
