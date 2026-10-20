module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.StalkGaloisAction
import StacksCheckRecall

open CategoryTheory Opposite
open AlgebraicGeometry

@[expose] public section

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale

/- 59.56.0.1 -/
@[stacks 04JK]
 #check (AlgebraicGeometry.Scheme.Etale.stalkGaloisAction :
    ∀ {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω],
      (s : Spec (.of Ω) ⟶ S) → (σ : Over.mk s ≅ Over.mk s) →
      (F : S.Etaleᵒᵖ ⥤ Type u) →
      (Scheme.pointSmallEtale s).presheafFiber.obj F →
        (Scheme.pointSmallEtale s).presheafFiber.obj F)

/- The action on a canonical stalk generator. -/
#check (AlgebraicGeometry.Scheme.Etale.stalkGaloisAction_on_generator :
    ∀ {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω],
      (s : Spec (.of Ω) ⟶ S) → (σ : Over.mk s ≅ Over.mk s) →
      (F : S.Etaleᵒᵖ ⥤ Type u) → (U : S.Etale) →
      (u : (Scheme.pointSmallEtale s).fiber.obj U) →
      (t : F.obj (op U)) →
      AlgebraicGeometry.Scheme.Etale.stalkGaloisAction s σ F
          ((Scheme.pointSmallEtale s).toPresheafFiber U u F t) =
        (Scheme.pointSmallEtale s).toPresheafFiber U
          ((AlgebraicGeometry.Scheme.Etale.geometricPointFiberMap s σ).app U u) F t)

/- The underlying scheme map of a transformed pointed lift. -/
#check (AlgebraicGeometry.Scheme.Etale.geometricPointFiberMap_app_left :
    ∀ {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω],
      (s : Spec (.of Ω) ⟶ S) → (σ : Over.mk s ≅ Over.mk s) →
      (U : S.Etale) → (u : (Scheme.pointSmallEtale s).fiber.obj U) →
      ((AlgebraicGeometry.Scheme.Etale.geometricPointFiberMap s σ).app U u).left =
        σ.hom.left ≫ u.left)

end AlgebraicGeometry.Scheme.Etale
