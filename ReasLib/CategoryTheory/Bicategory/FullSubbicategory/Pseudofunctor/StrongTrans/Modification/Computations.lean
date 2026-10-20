module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor.StrongTrans.Modification.Construction

/-!
# Computations for lifted modifications

Lifted modification components forget to their ambient components. The lift also preserves the
canonical identity and vertical composition of modifications.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

universe w v u wA vA uA

namespace ObjectProperty.FullSubbicategory.StrongTrans.Modification

variable {D : Type u} [Bicategory.{w, v} D]
variable {P : ObjectProperty D}
variable {A : Type uA} [Bicategory.{wA, vA} A]
variable (F G : Pseudofunctor A D)
variable (hF : ∀ X : A, P (F.obj X)) (hG : ∀ X : A, P (G.obj X))

/-- A lifted modification component is the ambient component with the induced-bicategory wrapper
added. -/
@[simp]
theorem liftPseudofunctor.app
    {η θ : Pseudofunctor.StrongTrans F G}
    (Γ : Pseudofunctor.StrongTrans.Modification η θ) (X : A) :
    (liftPseudofunctor F G hF hG Γ).app X =
      Bicategory.InducedBicategory.mkHom₂ (Γ.app X) := sorry

/-- Forgetting a lifted modification component recovers the ambient `2`-morphism. -/
@[simp]
theorem liftPseudofunctor.app.toAmbient
    {η θ : Pseudofunctor.StrongTrans F G}
    (Γ : Pseudofunctor.StrongTrans.Modification η θ) (X : A) :
    ((liftPseudofunctor F G hF hG Γ).app X).hom = Γ.app X := sorry

/-- Lifting modifications preserves the identity modification. -/
@[simp]
theorem liftPseudofunctor.id
    (η : Pseudofunctor.StrongTrans F G) :
    liftPseudofunctor F G hF hG
        (Pseudofunctor.StrongTrans.Modification.id η) =
      Pseudofunctor.StrongTrans.Modification.id
        (StrongTrans.liftPseudofunctor F G hF hG η) := sorry

/-- Lifting modifications preserves vertical composition. -/
@[simp]
theorem liftPseudofunctor.vcomp
    {η θ ι : Pseudofunctor.StrongTrans F G}
    (Γ : Pseudofunctor.StrongTrans.Modification η θ)
    (Δ : Pseudofunctor.StrongTrans.Modification θ ι) :
    liftPseudofunctor F G hF hG
        (Pseudofunctor.StrongTrans.Modification.vcomp Γ Δ) =
      Pseudofunctor.StrongTrans.Modification.vcomp
        (liftPseudofunctor F G hF hG Γ)
        (liftPseudofunctor F G hF hG Δ) := sorry

end ObjectProperty.FullSubbicategory.StrongTrans.Modification

end CategoryTheory
