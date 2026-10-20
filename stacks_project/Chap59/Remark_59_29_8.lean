module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.PointMorphism
import StacksCheckRecall

open CategoryTheory Opposite
open AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {S : Scheme.{u}} {K L : Type u} [Field K] [IsAlgClosed K] [Field L]
  [IsAlgClosed L]
variable {s : Spec (.of K) ⟶ S} {t : Spec (.of L) ⟶ S}

/- Remark 59.29.8: the canonical `Over` representation of the commuting
triangle gives the induced point morphism, neighborhood equivalence, and
natural stalk isomorphism. -/
@[stacks 04FN] #check (AlgebraicGeometry.Scheme.Etale.pointHom_presheafFiber_isIso :
    ∀ (a : Over.mk s ⟶ Over.mk t),
      IsIso ((AlgebraicGeometry.Scheme.Etale.pointHom a).presheafFiber
        (A := Type u)))

#check (AlgebraicGeometry.Scheme.Etale.pointHom :
    ∀ (a : Over.mk s ⟶ Over.mk t),
      Scheme.pointSmallEtale s ⟶ Scheme.pointSmallEtale t)

#check (AlgebraicGeometry.Scheme.Etale.pointPrecomp :
    ∀ (a : Over.mk s ⟶ Over.mk t),
      (Scheme.pointSmallEtale t).fiber.Elements ⥤
        (Scheme.pointSmallEtale s).fiber.Elements)

#check (AlgebraicGeometry.Scheme.Etale.pointHom_hom_app :
    ∀ (a : Over.mk s ⟶ Over.mk t) (U : S.Etale)
      (lift : (Scheme.pointSmallEtale t).fiber.obj U),
      ((AlgebraicGeometry.Scheme.Etale.pointHom a).hom.app U lift).left =
        a.left ≫ lift.left)

#check (AlgebraicGeometry.Scheme.Etale.pointPrecomp_obj :
    ∀ (a : Over.mk s ⟶ Over.mk t)
      (U : (Scheme.pointSmallEtale t).fiber.Elements),
      ((AlgebraicGeometry.Scheme.Etale.pointPrecomp a).obj U).1 = U.1)

#check (AlgebraicGeometry.Scheme.Etale.pointPrecomp_lift :
    ∀ (a : Over.mk s ⟶ Over.mk t)
      (U : (Scheme.pointSmallEtale t).fiber.Elements),
      ((AlgebraicGeometry.Scheme.Etale.pointPrecomp a).obj U).2.left =
        a.left ≫ U.2.left)

#check (AlgebraicGeometry.Scheme.Etale.pointPrecomp_map :
    ∀ (a : Over.mk s ⟶ Over.mk t)
      {U V : (Scheme.pointSmallEtale t).fiber.Elements} (f : U ⟶ V),
      ((AlgebraicGeometry.Scheme.Etale.pointPrecomp a).map f).val = f.val)

#check (AlgebraicGeometry.Scheme.Etale.pointHom_germ :
    ∀ (a : Over.mk s ⟶ Over.mk t) (F : S.Etaleᵒᵖ ⥤ Type u)
      (U : S.Etale) (lift : (Scheme.pointSmallEtale t).fiber.obj U)
      (σ : F.obj (op U)),
      (AlgebraicGeometry.Scheme.Etale.pointHom a).presheafFiber.app F
          ((Scheme.pointSmallEtale t).toPresheafFiber U lift F σ) =
        (Scheme.pointSmallEtale s).toPresheafFiber U
          ((AlgebraicGeometry.Scheme.Etale.pointHom a).hom.app U lift) F σ)

#check (AlgebraicGeometry.Scheme.Etale.pointPrecomp_isEquivalence :
    ∀ (a : Over.mk s ⟶ Over.mk t),
      (AlgebraicGeometry.Scheme.Etale.pointPrecomp a).IsEquivalence)

end AlgebraicGeometry.Scheme.Etale
