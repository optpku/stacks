/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Modification.Functoriality.Composition
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Modification.Functoriality.Identity
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.OppositeLocallyDiscrete
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

/-!
# Target-hom pseudofunctor for costructured-arrow postcomposition

For a fixed pseudofunctor `K : A ⥤ᵖ C` and objects `X Y : C`, target
postcomposition is contravariantly pseudofunctorial in the hom-category
`X ⟶ Y`. Its canonical domain is therefore the locally discrete bicategory
on `(X ⟶ Y)ᵒᵖ`.

The object action is `postcompose`, and a morphism of the opposite
hom-category acts through `postcompose.cellStrongTrans` after `unop`. Identity
and composition comparisons are the explicit owners from the functoriality
modules. This file only supplies the three remaining pseudofunctor coherence
statements. Its public computation formulas are in
`Modification.Pseudofunctor.Computations`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uA vA wA uC vC wC

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.ColaxCostructuredArrow

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {K : Pseudofunctor A C}
variable {X Y : C}

namespace Implementation

/-- The strong-transformation action of target postcomposition on a morphism
of the opposite target hom-category. -/
private def targetHomMap
    (K : Pseudofunctor A C) {f g : (X ⟶ Y)ᵒᵖ} (η : f ⟶ g) :
    Pseudofunctor.StrongTrans
      (postcompose K f.unop)
      (postcompose K g.unop) :=
  postcompose.cellStrongTrans K η.unop

/-- The identity comparison adapted to the opposite target hom-category. -/
private def targetHomMapId
    (K : Pseudofunctor A C) (f : (X ⟶ Y)ᵒᵖ) :=
  postcompose.cellMapId K f.unop

/-- The composition comparison adapted to the opposite target hom-category.

The arguments are reversed after `unop`, since composition in the opposite
category reverses vertical composition of target cells. -/
private def targetHomMapComp
    (K : Pseudofunctor A C) {f g h : (X ⟶ Y)ᵒᵖ}
    (η : f ⟶ g) (θ : g ⟶ h) :=
  postcompose.cellMapComp K θ.unop η.unop

/-- Explicit vertical composition in a target strong-transformation
hom-category, fixing the scoped modification-category universe in coherence
statements. -/
private def targetHomVcomp
    {F G : Pseudofunctor
      (ColaxCostructuredArrow K X)
      (ColaxCostructuredArrow K Y)}
    {η θ ι : Pseudofunctor.StrongTrans F G}
    (Γ : Pseudofunctor.StrongTrans.Hom η θ)
    (Δ : Pseudofunctor.StrongTrans.Hom θ ι) :
    Pseudofunctor.StrongTrans.Hom η ι :=
  Pseudofunctor.StrongTrans.Hom.of
    (Pseudofunctor.StrongTrans.Modification.vcomp Γ.as Δ.as)

/-- Associator coherence for target-hom postcomposition. -/
private theorem targetHomAssociator
    (K : Pseudofunctor A C) :
    ∀ {f g h i : (X ⟶ Y)ᵒᵖ}
      (η : f ⟶ g) (θ : g ⟶ h) (ι : h ⟶ i),
      targetHomVcomp
          (targetHomMapComp K (η ≫ θ) ι).hom
          (targetHomVcomp
            (Pseudofunctor.StrongTrans.whiskerRight
              (targetHomMapComp K η θ).hom
              (targetHomMap K ι))
            (targetHomVcomp
              (Pseudofunctor.StrongTrans.associator
                (targetHomMap K η)
                (targetHomMap K θ)
                (targetHomMap K ι)).hom
              (targetHomVcomp
                (Pseudofunctor.StrongTrans.whiskerLeft
                  (targetHomMap K η)
                  (targetHomMapComp K θ ι).inv)
                (targetHomMapComp K η (θ ≫ ι)).inv))) =
        eqToHom
          (congrArg
            (fun κ ↦ targetHomMap K κ)
            (Category.assoc η θ ι)) := sorry

/-- Left-unitor coherence for target-hom postcomposition. -/
private theorem targetHomLeftUnitor
    (K : Pseudofunctor A C) :
    ∀ {f g : (X ⟶ Y)ᵒᵖ} (η : f ⟶ g),
      targetHomVcomp
          (targetHomMapComp K (𝟙 f) η).hom
          (targetHomVcomp
            (Pseudofunctor.StrongTrans.whiskerRight
              (targetHomMapId K f).hom
              (targetHomMap K η))
            (Pseudofunctor.StrongTrans.leftUnitor
              (targetHomMap K η)).hom) =
        eqToHom
          (congrArg
            (fun κ ↦ targetHomMap K κ)
            (Category.id_comp η)) := sorry

/-- Right-unitor coherence for target-hom postcomposition. -/
private theorem targetHomRightUnitor
    (K : Pseudofunctor A C) :
    ∀ {f g : (X ⟶ Y)ᵒᵖ} (η : f ⟶ g),
      targetHomVcomp
          (targetHomMapComp K η (𝟙 g)).hom
          (targetHomVcomp
            (Pseudofunctor.StrongTrans.whiskerLeft
              (targetHomMap K η)
              (targetHomMapId K g).hom)
            (Pseudofunctor.StrongTrans.rightUnitor
              (targetHomMap K η)).hom) =
        eqToHom
          (congrArg
            (fun κ ↦ targetHomMap K κ)
            (Category.comp_id η)) := sorry

end Implementation

/-- Target postcomposition of colax costructured arrows as a pseudofunctor on
the opposite target hom-category.

Contravariance is absorbed into the domain `(X ⟶ Y)ᵒᵖ`; its morphism action
therefore has the ordinary pseudofunctor direction. -/
def postcompose.pseudofunctor
    (K : Pseudofunctor A C) (X Y : C) :
    LocallyDiscrete ((X ⟶ Y)ᵒᵖ) ⥤ᵖ
      Pseudofunctor
        (ColaxCostructuredArrow K X)
        (ColaxCostructuredArrow K Y) :=
  LocallyDiscrete.mkPseudofunctor
    (fun f ↦ postcompose K f.unop)
    (fun η ↦ Implementation.targetHomMap K η)
    (fun f ↦ Implementation.targetHomMapId K f)
    (fun η θ ↦ Implementation.targetHomMapComp K η θ)
    (Implementation.targetHomAssociator K)
    (Implementation.targetHomLeftUnitor K)
    (Implementation.targetHomRightUnitor K)

/- Data and axiom audit (mathlib 4.32):

`postcompose.pseudofunctor` is assembled by
`LocallyDiscrete.mkPseudofunctor`. Its object, morphism, identity-comparison,
and composition-comparison data are exactly the explicit owners imported from
the preceding modules. The three private helpers ending in `Associator` or
`Unitor` fill only `Prop`-valued pseudofunctor coherence fields; no
pseudofunctor, strong transformation, modification, or component `2`-cell is
selected through a proof placeholder. -/

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
