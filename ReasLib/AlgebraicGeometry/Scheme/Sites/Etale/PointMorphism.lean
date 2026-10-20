/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Category

open CategoryTheory Opposite
open AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {S : Scheme.{u}} {K L : Type u} [Field K] [IsAlgClosed K] [Field L]
  [IsAlgClosed L]
variable {s : Spec (.of K) ⟶ S} {t : Spec (.of L) ⟶ S}

/-- The morphism of small-étale site points induced by a morphism of geometric
points represented by an `Over` morphism. -/
noncomputable def pointHom (a : Over.mk s ⟶ Over.mk t) :
    Scheme.pointSmallEtale s ⟶ Scheme.pointSmallEtale t :=
  GrothendieckTopology.Point.Hom.mk
    (Functor.whiskerLeft (Etale.forget S) (coyoneda.map a.op))

/-- The neighborhood functor induced by precomposition with a geometric-point
morphism. -/
noncomputable def pointPrecomp (a : Over.mk s ⟶ Over.mk t) :
    (Scheme.pointSmallEtale t).fiber.Elements ⥤
      (Scheme.pointSmallEtale s).fiber.Elements :=
  NatTrans.mapElements (pointHom a).hom

/-- The underlying étale object of a precomposed pointed neighborhood is
unchanged. -/
theorem pointPrecomp_obj (a : Over.mk s ⟶ Over.mk t)
    (U : (Scheme.pointSmallEtale t).fiber.Elements) :
    ((pointPrecomp a).obj U).1 = U.1 := sorry

/-- The lift of a precomposed pointed neighborhood is obtained by composing
the original lift with the underlying morphism of `a`. -/
theorem pointPrecomp_lift (a : Over.mk s ⟶ Over.mk t)
    (U : (Scheme.pointSmallEtale t).fiber.Elements) :
    ((pointPrecomp a).obj U).2.left = a.left ≫ U.2.left := sorry

/-- The underlying étale morphism of a precomposed neighborhood morphism is
unchanged. -/
theorem pointPrecomp_map (a : Over.mk s ⟶ Over.mk t)
    {U V : (Scheme.pointSmallEtale t).fiber.Elements} (f : U ⟶ V) :
    ((pointPrecomp a).map f).val = f.val := sorry

/-- The underlying scheme morphism of the transformed fiber element is the
composite of the geometric-point morphism with the original lift. -/
theorem pointHom_hom_app (a : Over.mk s ⟶ Over.mk t) (U : S.Etale)
    (lift : (Scheme.pointSmallEtale t).fiber.obj U) :
    ((pointHom a).hom.app U lift).left = a.left ≫ lift.left := sorry

/-- The map on presheaf fibers sends a representative to the representative
with its lift precomposed by the geometric-point morphism. -/
theorem pointHom_germ (a : Over.mk s ⟶ Over.mk t) (F : S.Etaleᵒᵖ ⥤ Type u)
    (U : S.Etale) (lift : (Scheme.pointSmallEtale t).fiber.obj U)
    (σ : F.obj (op U)) :
    (pointHom a).presheafFiber.app F
        ((Scheme.pointSmallEtale t).toPresheafFiber U lift F σ) =
      (Scheme.pointSmallEtale s).toPresheafFiber U
        ((pointHom a).hom.app U lift) F σ := sorry

/-- Precomposition on pointed neighborhoods is an equivalence for a morphism
between geometric points. -/
instance pointPrecomp_isEquivalence (a : Over.mk s ⟶ Over.mk t) :
    (pointPrecomp a).IsEquivalence := sorry

/-- The natural transformation on presheaf fibers induced by a morphism of
geometric points is an isomorphism. -/
instance pointHom_presheafFiber_isIso (a : Over.mk s ⟶ Over.mk t) :
    IsIso ((pointHom a).presheafFiber (A := Type u)) := sorry

end AlgebraicGeometry.Scheme.Etale
