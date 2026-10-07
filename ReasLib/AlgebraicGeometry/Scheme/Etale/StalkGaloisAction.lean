module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Category

open CategoryTheory Opposite
open AlgebraicGeometry

@[expose] public section

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The automorphism of a geometric point acts on pointed étale neighborhoods by
precomposing their chosen lifts with the underlying map of the automorphism. -/
noncomputable def geometricPointFiberMap
    (s : Spec (.of Ω) ⟶ S) (σ : Over.mk s ≅ Over.mk s) :
    (Scheme.pointSmallEtale s).fiber ⟶ (Scheme.pointSmallEtale s).fiber :=
  Functor.whiskerLeft (Etale.forget S) (coyoneda.map σ.hom.op)

/-- The automorphism of a geometric point induces an endomorphism of every
presheaf fiber on the small étale site. -/
noncomputable def stalkGaloisAction
    (s : Spec (.of Ω) ⟶ S) (σ : Over.mk s ≅ Over.mk s)
    (F : S.Etaleᵒᵖ ⥤ Type u) :
    (Scheme.pointSmallEtale s).presheafFiber.obj F →
      (Scheme.pointSmallEtale s).presheafFiber.obj F :=
  (GrothendieckTopology.Point.Hom.presheafFiber
    (⟨geometricPointFiberMap s σ⟩ :
      Scheme.pointSmallEtale s ⟶ Scheme.pointSmallEtale s)).app F

/-- The induced stalk endomorphism sends a canonical generator to the generator
whose pointed lift is transformed by the geometric-point automorphism. -/
theorem stalkGaloisAction_on_generator
    (s : Spec (.of Ω) ⟶ S) (σ : Over.mk s ≅ Over.mk s)
    (F : S.Etaleᵒᵖ ⥤ Type u) (U : S.Etale)
    (u : (Scheme.pointSmallEtale s).fiber.obj U) (t : F.obj (op U)) :
    stalkGaloisAction s σ F
        ((Scheme.pointSmallEtale s).toPresheafFiber U u F t) =
      (Scheme.pointSmallEtale s).toPresheafFiber U
        ((geometricPointFiberMap s σ).app U u) F t := sorry

/-- The underlying scheme map of the transformed pointed lift is the composite
of the automorphism's underlying map with the original lift. -/
theorem geometricPointFiberMap_app_left
    (s : Spec (.of Ω) ⟶ S) (σ : Over.mk s ≅ Over.mk s)
    (U : S.Etale) (u : (Scheme.pointSmallEtale s).fiber.obj U) :
    ((geometricPointFiberMap s σ).app U u).left = σ.hom.left ≫ u.left := sorry

end AlgebraicGeometry.Scheme.Etale
