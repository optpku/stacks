/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap103.Lemma_103_17_7_Serre
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Limits CategoryTheory.ObjectProperty GroupoidsOver

universe u

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]

/- Lemma 103.17.7 (1): let `X` be a locally Noetherian algebraic stack. Then
`Coh(𝒪_X)` is a Serre subcategory of `QCoh(𝒪_X)`. -/
@[stacks 0GRB]
#check (Coh.isSerreClass :
  ((coherentModuleProperty X).inverseImage (QCoh.inclusion X)).IsSerreClass)

variable {F G : QCoh X} (φ : F ⟶ G) [Epi φ] [AlgebraicStack.IsCoherent F.obj] in
/- Lemma 103.17.7 (2): if `F` is coherent and `φ` is surjective, then `G` is
coherent. -/
@[stacks 0GRB]
#check (isCoherent_of_epi φ : AlgebraicStack.IsCoherent G.obj)

variable {F G : QCoh X} (φ : F ⟶ G) [AlgebraicStack.IsCoherent F.obj] in
/- Lemma 103.17.7 (3): if `F` is coherent, then `Im(φ)` is coherent. -/
@[stacks 0GRB]
#check (isCoherent_image_of_qCohHom φ :
  AlgebraicStack.IsCoherent (Abelian.image ((QCoh.inclusion X).map φ)))

variable {F G : QCoh X} (φ : F ⟶ G) [AlgebraicStack.IsCoherent G.obj]
  [IsParasitic (kernel ((QCoh.inclusion X).map φ)).val] in
/- Lemma 103.17.7 (4): if `G` is coherent and `Ker(φ)` is parasitic, then `F`
is coherent. -/
@[stacks 0GRB]
#check (isCoherent_of_isParasitic_kernel φ : AlgebraicStack.IsCoherent F.obj)
