/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DescentData.Effectivity
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

variable {I : Type v} {S : Scheme.{u}} {X : AlgebraicSpace S}
variable (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)

/- Definition 74.22.11: A descent datum is effective when it is isomorphic to the
canonical pullback datum of an algebraic space over the fixed target. -/
@[stacks 0ADR] #check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.IsEffective :
    DescentData Xᵢ f → Prop)

#check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.isEffective_iff :
    ∀ D : DescentData Xᵢ f,
      D.IsEffective ↔ ∃ U : Over X, Nonempty (DescentData.ofObj Xᵢ f U ≅ D))

#check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.IsEffective.ofObj :
    ∀ U : Over X, DescentData.IsEffective (DescentData.ofObj Xᵢ f U))

#check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.IsEffective.ofIso :
    ∀ {D E : DescentData Xᵢ f}, (D ≅ E) → D.IsEffective → E.IsEffective)

#check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.trivial :
    Over X → DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ 𝟙 X))

#check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.trivial_obj_obj :
    ∀ U : Over X, (DescentData.trivial U).obj ⟨⟩ = (overPullback (𝟙 X)).obj U)

#check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.trivialPullback Xᵢ f :
    DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ 𝟙 X) ⥤ DescentData Xᵢ f)

#check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.trivialPullback_obj_obj Xᵢ f :
    ∀ (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ 𝟙 X)) (i : I),
      ((DescentData.trivialPullback Xᵢ f).obj D).obj i =
        (overPullback (f i)).obj (D.obj ⟨⟩))

#check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.ofObjIsoPullbackTrivial Xᵢ f :
    ∀ U : Over X, DescentData.ofObj Xᵢ f U ≅
      (DescentData.trivialPullback Xᵢ f).obj (DescentData.trivial U))

#check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.ofObjIsoPullbackTrivial_hom_hom Xᵢ f :
    ∀ (U : Over X) (i : I),
      (DescentData.ofObjIsoPullbackTrivial Xᵢ f U).hom.hom i =
        ((overPseudofunctor S).map (f i).op.toLoc).toFunctor.map
          ((Cat.Hom.toNatIso
            ((overPseudofunctor S).mapId' (𝟙 X).op.toLoc)).inv.app U))
