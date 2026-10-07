module

public import ReasLib.AlgebraicGeometry.Scheme.EtaleCohomology.GabberH0
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/- Lemma 59.82.2: if `X` is qcqs, `i : Z ⟶ X` is a closed immersion, Zariski global
sections restrict bijectively along `i`, and this persists after any finite base
change `X' ⟶ X` for `Z ×_X X' ⟶ X'`, then étale global sections of any sheaf of
sets on `X_étale` identify with those of `i_small⁻¹ F` on `Z`. -/
@[stacks 09ZF] #check
  (AlgebraicGeometry.Scheme.etaleGlobalSections_bijective_of_zariskiFiniteBaseChange :
    ∀ {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (i : Z ⟶ X)
      [IsClosedImmersion i]
      [HasWeakSheafify X.smallZariskiTopology (Type (u + 1))]
      [HasWeakSheafify Z.smallZariskiTopology (Type (u + 1))]
      [∀ P : X.smallZariskiSiteᵒᵖ ⥤ Type (u + 1),
        (smallZariskiPullback i).op.HasLeftKanExtension P]
      [HasWeakSheafify X.smallEtaleTopology (Type u)]
      [HasWeakSheafify Z.smallEtaleTopology (Type u)]
      [∀ P : X.Etaleᵒᵖ ⥤ Type u, (smallEtalePullback i).op.HasLeftKanExtension P]
      (h_zar : zariskiGlobalSections_bijective i)
      (h_fin : ∀ {X' : Scheme.{u}} (f : X' ⟶ X) [IsFinite f]
        [HasWeakSheafify X'.smallZariskiTopology (Type (u + 1))]
        [HasWeakSheafify (pullback i f).smallZariskiTopology (Type (u + 1))]
        [∀ P : X'.smallZariskiSiteᵒᵖ ⥤ Type (u + 1),
          (smallZariskiPullback (pullback.snd i f)).op.HasLeftKanExtension P],
        zariskiGlobalSections_bijective (pullback.snd i f))
      (F : Sheaf X.smallEtaleTopology (Type u)),
      Function.Bijective (etaleGlobalSectionsPullback i F))
