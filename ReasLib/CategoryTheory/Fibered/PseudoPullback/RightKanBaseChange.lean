module
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.CostructuredArrow
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Symmetry.Swap.Construction
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped BasedFunctor
noncomputable section
universe u v uX vX uY vY uS vS uA vA
namespace CategoryTheory.BasedCategory.PseudoPullback.RightKanBaseChange
variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}
variable (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
variable [Functor.IsFibered.InGroupoids X.p] [Functor.IsFibered.InGroupoids S.p]
open BasedCategory.PseudoPullback

/-- Reverse indices retain the original second object and use the actual first-side Cartesian lift. -/
def reverseIndex (x : X.obj) (a : StructuredArrow (op (F.obj x)) G.toFunctor.op) :
    StructuredArrow (op x) (fst F G).toFunctor.op :=
  StructuredArrow.mk (Y := op ((swap G F).obj
      (CostructuredArrow.reversePair G F x
        (CategoryTheory.CostructuredArrow.mk a.hom.unop))))
    (CostructuredArrow.reverseArrow G F x
      (CategoryTheory.CostructuredArrow.mk a.hom.unop)).op

variable {A : Type uA} [Category.{vA} A]
variable (P : Y.objᵒᵖ ⥤ A)
abbrev originalDiagram (x : X.obj) :=
  StructuredArrow.proj (op (F.obj x)) G.toFunctor.op ⋙ P
abbrev changedDiagram (x : X.obj) :=
  StructuredArrow.proj (op x) (fst F G).toFunctor.op ⋙ (snd F G).toFunctor.op ⋙ P

/-- Compatible section families descend along the displayed reverse indices. -/
def reverseLimit (x : X.obj) [HasLimit (originalDiagram F G P x)]
    [HasLimit (changedDiagram F G P x)] :
    limit (changedDiagram F G P x) ⟶ limit (originalDiagram F G P x) :=
  limit.lift (originalDiagram F G P x)
    { pt := limit (changedDiagram F G P x)
      π := { app a := limit.π (changedDiagram F G P x) (reverseIndex F G x a)
             naturality := sorry } }

variable [∀ P : Y.objᵒᵖ ⥤ A, G.toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ Q : (BasedCategory.PseudoPullback F G).objᵒᵖ ⥤ A,
  (fst F G).toFunctor.op.HasPointwiseRightKanExtension Q]

/-- Native pointwise Kan comparisons and the actual reverse family map give the reverse component. -/
def reverseComponent (x : X.obj) :
    ((fst F G).toFunctor.op.ran.obj ((snd F G).toFunctor.op ⋙ P)).obj (op x) ⟶
      (G.toFunctor.op.ran.obj P).obj (op (F.obj x)) :=
  ((fst F G).toFunctor.op.ranObjObjIsoLimit ((snd F G).toFunctor.op ⋙ P) (op x)).hom ≫
    reverseLimit F G P x ≫
    (G.toFunctor.op.ranObjObjIsoLimit P (op (F.obj x))).inv

/-- Forward indices use the supplied comparison isomorphism and given first-projection arrow. -/
def forwardIndex (x : X.obj) (a : StructuredArrow (op x) (fst F G).toFunctor.op) :
    StructuredArrow (op (F.obj x)) G.toFunctor.op :=
  StructuredArrow.mk (Y := op (sndObj a.right.unop))
    ((comparisonIsoApp a.right.unop).inv ≫ F.map a.hom.unop).op

/-- Forward transport reads each family at the explicit forward comma index. -/
def forwardLimit (x : X.obj) [HasLimit (originalDiagram F G P x)]
    [HasLimit (changedDiagram F G P x)] :
    limit (originalDiagram F G P x) ⟶ limit (changedDiagram F G P x) :=
  limit.lift (changedDiagram F G P x)
    { pt := limit (originalDiagram F G P x)
      π := { app a := limit.π (originalDiagram F G P x) (forwardIndex F G x a)
             naturality := sorry } }

/-- The ordinary base-change map stores the actual forward compatible-section map. -/
def forwardComponent (x : X.obj) :
    (G.toFunctor.op.ran.obj P).obj (op (F.obj x)) ⟶
      ((fst F G).toFunctor.op.ran.obj ((snd F G).toFunctor.op ⋙ P)).obj (op x) :=
  (G.toFunctor.op.ranObjObjIsoLimit P (op (F.obj x))).hom ≫
    forwardLimit F G P x ≫
    ((fst F G).toFunctor.op.ranObjObjIsoLimit ((snd F G).toFunctor.op ⋙ P) (op x)).inv

/-- The actual forward and reverse section maps are mutually inverse. -/
def componentIso (x : X.obj) :
    (G.toFunctor.op.ran.obj P).obj (op (F.obj x)) ≅
      ((fst F G).toFunctor.op.ran.obj ((snd F G).toFunctor.op ⋙ P)).obj (op x) where
  hom := forwardComponent F G P x
  inv := reverseComponent F G P x
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Base change on presheaves, with both maps given by the displayed comma-index formulas. -/
def presheafIso :
    F.toFunctor.op ⋙ G.toFunctor.op.ran.obj P ≅
      (fst F G).toFunctor.op.ran.obj ((snd F G).toFunctor.op ⋙ P) :=
  NatIso.ofComponents (fun x ↦ componentIso F G P x.unop) (by sorry)

end CategoryTheory.BasedCategory.PseudoPullback.RightKanBaseChange
