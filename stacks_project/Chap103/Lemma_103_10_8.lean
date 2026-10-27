/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.InternalHom.FinitePresentation
import StacksCheckRecall

/-!
# Lemma 103.10.8

On an algebraic stack, sheaf Hom from a finitely presented `𝒪_X`-module into a
quasi-coherent module agrees in `Mod(X_étale, 𝒪_X)` and `Mod(𝒪_X)`, lies in
`LQCoh^{fbc}(𝒪_X)`, and its image under `Q` represents `Hom(H ⊗ F, G)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory

universe u

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
variable (F : fppfModules X) (G H : QCoh X) [F.IsFinitePresentation]

/- Lemma 103.10.8 (1): the internal Homs computed in the fppf and étale module categories agree. -/
@[stacks 0GQN] #check
  (AlgebraicGeometry.GroupoidsOver.moduleSheafHom_restrictionIso F G.obj :
    (restriction X).obj (moduleSheafHomFppf F G.obj) ≅
      moduleSheafHomEtale ((restriction X).obj F) ((restriction X).obj G.obj))

/- Lemma 103.10.8 (2): the common value is locally quasi-coherent with flat base change. -/
@[stacks 0GQN] #check
  (AlgebraicGeometry.GroupoidsOver.moduleSheafHomOnEtale_mem_lqcohFbc F G :
    lqcohFbc X (moduleSheafHomEtale ((restriction X).obj F) ((restriction X).obj G.obj)))

/- Lemma 103.10.8 (3): the quasi-coherent internal Hom is Q of the common sheaf Hom. -/
@[stacks 0GQN] #check
  (AlgebraicGeometry.GroupoidsOver.QCoh.internalHomFP_eq F G :
    QCoh.internalHomFP F G = (LQCohFbc.toQCoh X).obj (moduleSheafHomLQCohFbc F G))

/- Lemma 103.10.8 (4): the quasi-coherent internal Hom represents Hom_X(H ⊗ F, G). -/
@[stacks 0GQN] #check
  (AlgebraicGeometry.GroupoidsOver.QCoh.internalHomFP_fppfHomEquiv F G H :
    (H ⟶ QCoh.internalHomFP F G) ≃ (moduleTensorFppf H.obj F ⟶ G.obj))
