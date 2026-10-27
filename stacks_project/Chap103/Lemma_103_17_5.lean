/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.Abelian
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Limits GroupoidsOver

universe u

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]

/- Lemma 103.17.5 (1): let `X` be a locally Noetherian algebraic stack. The
category of coherent `𝒪_X`-modules is abelian. -/
@[stacks 0GR9]
#check (AlgebraicGeometry.AlgebraicStack.Coh.abelian : Abelian (Coh X))

variable {F G : SheafOfModules.{u} (structureSheaf X)}
  [AlgebraicStack.IsCoherent F] [AlgebraicStack.IsCoherent G] (φ : F ⟶ G) in
/- Lemma 103.17.5 (2): the cokernel of a map of coherent `𝒪_X`-modules,
computed in `Mod(𝒪_X)`, is coherent. -/
@[stacks 0GR9]
#check (AlgebraicGeometry.AlgebraicStack.isCoherent_cokernel φ :
  AlgebraicStack.IsCoherent (cokernel φ))

variable {F G : SheafOfModules.{u} (structureSheaf X)}
  [AlgebraicStack.IsCoherent F] [AlgebraicStack.IsCoherent G] (φ : F ⟶ G) in
/- Lemma 103.17.5 (3): the image of a map of coherent `𝒪_X`-modules, computed
in `Mod(𝒪_X)`, is coherent. -/
@[stacks 0GR9]
#check (AlgebraicGeometry.AlgebraicStack.isCoherent_image φ :
  AlgebraicStack.IsCoherent (Abelian.image φ))

variable {F G : Coh X} (φ : F ⟶ G) in
/- Lemma 103.17.5 (4): the kernel of a map of coherent `𝒪_X`-modules, computed
in `Mod(𝒪_X)`, may not be coherent, but it lies in `LQCoh^{fbc}(𝒪_X)`. -/
@[stacks 0GR9]
#check (AlgebraicGeometry.GroupoidsOver.QCoh.kernel_mem_lqcohFbc (Coh.toQCoh.map φ) :
  FppfModules.lqcohFbc X (kernel ((Coh.inclusion X).map φ)))

variable {F G : Coh X} (φ : F ⟶ G) in
/- Lemma 103.17.5 (5): `Q(Ker(φ))` is a coherent `𝒪_X`-module. -/
@[stacks 0GR9]
#check (AlgebraicGeometry.AlgebraicStack.isCoherent_toQCoh_fppf_kernel φ :
  AlgebraicStack.IsCoherent
    ((QCoh.inclusion X).obj
      ((LQCohFbc.toQCoh X).obj (QCoh.kernelLQCohFbc (Coh.toQCoh.map φ)))))

variable {F G : Coh X} (φ : F ⟶ G) in
/- Lemma 103.17.5 (6): `Q(Ker(φ))` is the kernel of `φ` in `Coh(𝒪_X)`. -/
@[stacks 0GR9]
#check (AlgebraicGeometry.AlgebraicStack.Coh.kernelIso_toQCoh_fppf φ :
  Coh.toQCoh.obj (kernel φ) ≅
    (LQCohFbc.toQCoh X).obj (QCoh.kernelLQCohFbc (Coh.toQCoh.map φ)))

/- Lemma 103.17.5 (7): the inclusion functor `Coh(𝒪_X) ⟶ QCoh(𝒪_X)` is exact. -/
@[stacks 0GR9]
#check (AlgebraicGeometry.AlgebraicStack.Coh.toQCoh_exact :
  exactFunctor (Coh X) (QCoh X) Coh.toQCoh)
