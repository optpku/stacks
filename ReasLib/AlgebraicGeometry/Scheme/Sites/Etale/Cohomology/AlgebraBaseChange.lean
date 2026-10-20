module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AlgebraBaseChange
public import ReasLib.CategoryTheory.Sites.Cohomology.Map

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.AlgebraBaseChange

open AlgebraicGeometry.Scheme.AlgebraBaseChange

variable {I : Type u} [Preorder I] [Nonempty I]
variable (A : CommRingCat.{u}) (B : I ⥤ CommRingCat.{u})
variable (σ : (Functor.const I).obj A ⟶ B)
variable {X : Scheme.{u}} (f : X ⟶ Scheme.Spec.obj (op A))
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasSheafify (stage A B σ f i).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (stage A B σ f i).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasExt.{u} (Sheaf (stage A B σ f i).smallEtaleTopology AddCommGrpCat.{u})]
variable [HasColimit B]
variable [HasSheafify (limit A B σ f).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify (limit A B σ f).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (limit A B σ f).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {S T : Scheme.{u}} (g : T ⟶ S),
    ((smallEtalePullback g).sheafPushforwardContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
variable (p : ℕ)

section

variable [IsDirected I (· ≤ ·)]

/-- The cohomology map induced by a transition between two stage inverse images. -/
def cohomologyMap {i j : I} (hij : i ≤ j) :
    (stageSheaf A B σ f F i).H' p (globalEtale (stage A B σ f i)) ⟶
      (stageSheaf A B σ f F j).H' p (globalEtale (stage A B σ f j)) :=
  cohomologyPullback (transition A B σ f hij) (stageSheaf A B σ f F i) p ≫
    Sheaf.cohomologyMap (transitionIso A B σ f F hij).hom p
      (globalEtale (stage A B σ f j))

/-- The stage cohomology maps satisfy the identity law. -/
theorem cohomologyMap_id (i : I) :
    cohomologyMap A B σ f F p (le_refl i) = 𝟙 _ := sorry

/-- The stage cohomology maps satisfy the composition law. -/
theorem cohomologyMap_comp {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    cohomologyMap A B σ f F p (hij.trans hjk) =
      cohomologyMap A B σ f F p hij ≫ cohomologyMap A B σ f F p hjk := sorry

/-- The directed diagram of degree-`p` étale cohomology groups of the stages. -/
def cohomologyDiagram : I ⥤ AddCommGrpCat.{u} where
  obj i := (stageSheaf A B σ f F i).H' p (globalEtale (stage A B σ f i))
  map {_ _} hij := cohomologyMap A B σ f F p (leOfHom hij)
  map_id := cohomologyMap_id A B σ f F p
  map_comp := fun {_ _ _} hij hjk =>
    cohomologyMap_comp A B σ f F p (leOfHom hij) (leOfHom hjk)

/-- Evaluation of the cohomology diagram at a stage is its degree-`p` cohomology group. -/
theorem cohomologyDiagram_obj (i : I) :
    (cohomologyDiagram A B σ f F p).obj i =
      (stageSheaf A B σ f F i).H' p (globalEtale (stage A B σ f i)) := sorry

/-- The map from a stage cohomology group to the cohomology of the colimit base change. -/
def comparisonLeg (i : I) :
    (stageSheaf A B σ f F i).H' p (globalEtale (stage A B σ f i)) ⟶
      (limitSheaf A B σ f F).H' p (globalEtale (limit A B σ f)) :=
  cohomologyPullback (fromLimit A B σ f i) (stageSheaf A B σ f F i) p ≫
    Sheaf.cohomologyMap (fromLimitIso A B σ f F i).hom p
      (globalEtale (limit A B σ f))

/-- The stage-to-limit cohomology maps form a cocone over the stage diagram. -/
theorem comparisonLeg_naturality {i j : I} (hij : i ≤ j) :
    cohomologyMap A B σ f F p hij ≫ comparisonLeg A B σ f F p j =
      comparisonLeg A B σ f F p i := sorry

/-- The canonical map from the colimit of stage cohomology to limit cohomology. -/
def comparison [HasColimit (cohomologyDiagram A B σ f F p)] :
    colimit (cohomologyDiagram A B σ f F p) ⟶
      (limitSheaf A B σ f F).H' p (globalEtale (limit A B σ f)) :=
  colimit.desc (cohomologyDiagram A B σ f F p)
    { pt := (limitSheaf A B σ f F).H' p (globalEtale (limit A B σ f))
      ι :=
        { app := fun i => comparisonLeg A B σ f F p i
          naturality := fun i _ hij =>
            (comparisonLeg_naturality A B σ f F p (leOfHom hij)).trans
              (Category.comp_id (comparisonLeg A B σ f F p i)).symm } }

/-- The canonical comparison restricts on each colimit inclusion to its stage leg. -/
theorem comparison_ι [HasColimit (cohomologyDiagram A B σ f F p)] (i : I) :
    colimit.ι (cohomologyDiagram A B σ f F p) i ≫ comparison A B σ f F p =
      comparisonLeg A B σ f F p i := sorry

end

/-- The canonical algebra-base-change comparison is an isomorphism for qcqs `f`. -/
instance comparison_isIso [IsDirected I (· ≤ ·)] [QuasiCompact f] [QuasiSeparated f]
    [HasColimit (cohomologyDiagram A B σ f F p)] :
    IsIso (comparison A B σ f F p) := sorry

end AlgebraicGeometry.Scheme.Etale.AlgebraBaseChange

end
