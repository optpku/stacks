module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.FilteredColimit

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (F : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
variable (p : ℕ)
variable [HasColimit F] [HasColimit (sheafCohomologyDiagram F p)]

/- Lemma 59.51.4: on a quasi-compact and quasi-separated scheme `X`, filtered colimits
of abelian sheaves on `X_étale` commute with global étale cohomology. Equivalently, the
comparison `colim_i H^p_étale(X, F_i) ⟶ H^p_étale(X, colim_i F_i)` is an isomorphism
for every `p ≥ 0`. -/
@[stacks 03Q5] #check
  (AlgebraicGeometry.Scheme.Etale.etaleCohomology_colimit (F := F) (p := p) :
    IsIso (AlgebraicGeometry.Scheme.Etale.sheafCohomologyComparison F p))

end AlgebraicGeometry.Scheme.Etale

end
