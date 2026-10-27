/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered

/-! # Extension of right exact tensor functors from coherent modules

The extension preserves all colimits of the ambient module universe. The natural
abstract generalization is extension from finitely presentable filtered
generators with tensor products commuting with colimits; the geometric
statements here impose no extra smallness hypotheses on coherent modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A right exact functor on coherent modules of Noetherian algebraic stacks
with a natural tensor comparison extends to a colimit-preserving functor on
quasi-coherent modules whose tensor comparison restricts to the given one. -/
theorem exists_extend_rightExactTensor
    {S₁ S₂ : Scheme.{u}} {X : GroupoidsOver S₁} {Y : GroupoidsOver S₂}
    [AlgebraicStack X] [IsNoetherian X] [AlgebraicStack Y] [IsNoetherian Y]
    (F : Coh X ⥤ Coh Y) [PreservesFiniteColimits F]
    (T : Coh.tensorBifunctor X ⋙ F ≅ Functor.prod F F ⋙ Coh.tensorBifunctor Y) :
    ∃ G : QCoh X ⥤ QCoh Y,
      PreservesColimitsOfSize.{u, u} G ∧
        ∃ (e : (Coh.toQCoh : Coh X ⥤ QCoh X) ⋙ G ≅
            F ⋙ (Coh.toQCoh : Coh Y ⥤ QCoh Y))
          (U : QCoh.Fppf.tensorBifunctor X ⋙ G ≅
            Functor.prod G G ⋙ QCoh.Fppf.tensorBifunctor Y),
          ∀ A B : Coh X,
            U.hom.app (Coh.toQCoh.obj A, Coh.toQCoh.obj B) ≫
                QCoh.Fppf.tensorMap (e.hom.app A) (e.hom.app B) =
              G.map (Coh.tensor_toQCohIso A B).inv ≫
                e.hom.app (Coh.tensor A B) ≫
                Coh.toQCoh.map (T.hom.app (A, B)) ≫
                (Coh.tensor_toQCohIso (F.obj A) (F.obj B)).hom :=
  sorry

/-- Two filtered-colimit-preserving functors on quasi-coherent modules of
Noetherian algebraic stacks are naturally isomorphic when their restrictions
to coherent modules are identified with the same functor. -/
theorem extend_rightExactTensor_unique
    {S₁ S₂ : Scheme.{u}} {X : GroupoidsOver S₁} {Y : GroupoidsOver S₂}
    [AlgebraicStack X] [IsNoetherian X] [AlgebraicStack Y] [IsNoetherian Y]
    (F : Coh X ⥤ Coh Y) (G G' : QCoh X ⥤ QCoh Y)
    (hG : PreservesFilteredColimitsOfSize.{u, u} G)
    (hG' : PreservesFilteredColimitsOfSize.{u, u} G')
    (e : (Coh.toQCoh : Coh X ⥤ QCoh X) ⋙ G ≅
      F ⋙ (Coh.toQCoh : Coh Y ⥤ QCoh Y))
    (e' : (Coh.toQCoh : Coh X ⥤ QCoh X) ⋙ G' ≅
      F ⋙ (Coh.toQCoh : Coh Y ⥤ QCoh Y)) :
    Nonempty (G ≅ G') :=
  sorry

/-- A right exact tensor functor between coherent modules of Noetherian
algebraic stacks extends to a tensor-compatible colimit-preserving functor on
quasi-coherent modules, uniquely up to natural isomorphism among extensions
preserving filtered colimits. -/
theorem existsUnique_extend_rightExactTensor
    {S₁ S₂ : Scheme.{u}} {X : GroupoidsOver S₁} {Y : GroupoidsOver S₂}
    [AlgebraicStack X] [IsNoetherian X] [AlgebraicStack Y] [IsNoetherian Y]
    (F : Coh X ⥤ Coh Y) [PreservesFiniteColimits F]
    (T : Coh.tensorBifunctor X ⋙ F ≅ Functor.prod F F ⋙ Coh.tensorBifunctor Y) :
    ∃ G : QCoh X ⥤ QCoh Y,
      PreservesColimitsOfSize.{u, u} G ∧
        ∃ (e : (Coh.toQCoh : Coh X ⥤ QCoh X) ⋙ G ≅
            F ⋙ (Coh.toQCoh : Coh Y ⥤ QCoh Y))
          (U : QCoh.Fppf.tensorBifunctor X ⋙ G ≅
            Functor.prod G G ⋙ QCoh.Fppf.tensorBifunctor Y),
          (∀ A B : Coh X,
            U.hom.app (Coh.toQCoh.obj A, Coh.toQCoh.obj B) ≫
                QCoh.Fppf.tensorMap (e.hom.app A) (e.hom.app B) =
              G.map (Coh.tensor_toQCohIso A B).inv ≫
                e.hom.app (Coh.tensor A B) ≫
                Coh.toQCoh.map (T.hom.app (A, B)) ≫
                (Coh.tensor_toQCohIso (F.obj A) (F.obj B)).hom) ∧
          ∀ G' : QCoh X ⥤ QCoh Y,
            PreservesFilteredColimitsOfSize.{u, u} G' →
              Nonempty ((Coh.toQCoh : Coh X ⥤ QCoh X) ⋙ G' ≅
                F ⋙ (Coh.toQCoh : Coh Y ⥤ QCoh Y)) →
              Nonempty (G ≅ G') :=
  sorry

end AlgebraicGeometry.AlgebraicStack
