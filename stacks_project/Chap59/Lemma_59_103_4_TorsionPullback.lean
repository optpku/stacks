/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HComparison

/-- Abelian-group-valued sheafification exists on the small étale site at the
coefficient universe used by topology comparison. -/
instance smallEtale_hasSheafify_addCommGrp (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1} := sorry

/-- Abelian-group-valued sheafification exists on every big étale slice at the
coefficient universe used by topology comparison. -/
instance etaleOver_hasSheafify_addCommGrp (X : Scheme.{u}) :
    HasSheafify (etaleTopology.over X) AddCommGrpCat.{u + 1} := sorry

/-- Étale relocalization admits left Kan extensions on abelian presheaves at the
topology-comparison coefficient universe. -/
instance relocalizationFunctor_op_hasLeftKanExtension_addCommGrp
    {S T : Scheme.{u}} (f : T ⟶ S) (P : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (relocalizationFunctor f).op.HasLeftKanExtension P := sorry

/-- Inverse image `π_X⁻¹` on abelian sheaves from the small étale site of `X` to
the big étale slice `(Sch/X)_étale`. -/
def piInverseImage (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1} :=
  (relocalizationFunctor (𝟙 X)).sheafPullback AddCommGrpCat.{u + 1}
    X.smallEtaleTopology (etaleTopology.over X)

/-- Inverse image `π_X⁻¹` is the sheaf pullback along identity-base étale
relocalization. -/
theorem piInverseImage_eq_sheafPullback (X : Scheme.{u}) :
    piInverseImage X =
      (relocalizationFunctor (𝟙 X)).sheafPullback AddCommGrpCat.{u + 1}
        X.smallEtaleTopology (etaleTopology.over X) := sorry

/-- The coefficient family `A'_X`: sheaves on `(Sch/X)_étale` isomorphic to
`π_X⁻¹ F` for a torsion abelian sheaf `F` on `X_étale`. -/
abbrev torsionPullback (X : Scheme.{u}) :
    ObjectProperty (Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1}) :=
  (Sheaf.torsion X.smallEtaleTopology).map (piInverseImage X)

/-- Membership in `torsionPullback X` means the sheaf is isomorphic to the
inverse image of a locally torsion small-étale abelian sheaf. -/
theorem torsionPullback_mem_iff {X : Scheme.{u}}
    {F : Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1}} :
    torsionPullback X F ↔
      ∃ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
        G.IsLocallyTorsion ∧ Nonempty ((piInverseImage X).obj G ≅ F) := sorry

/-- The inverse image of a locally torsion small-étale sheaf lies in
`torsionPullback`. -/
theorem obj_mem_torsionPullback {X : Scheme.{u}}
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hG : G.IsLocallyTorsion) :
    torsionPullback X ((piInverseImage X).obj G) := sorry

/-- The family `A'_X` is a weak Serre class in `Ab((Sch/X)_étale)`. -/
instance torsionPullback_isWeakSerre (X : Scheme.{u}) :
    IsWeakSerreClass (torsionPullback X) := sorry

end AlgebraicGeometry.Scheme.HComparison

end

end
