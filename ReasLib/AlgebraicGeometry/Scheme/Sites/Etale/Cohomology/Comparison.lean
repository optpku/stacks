/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Units
public import ReasLib.AlgebraicGeometry.Scheme.Sites.FunctionSheaves
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Cohomology
public import Mathlib.Algebra.Category.Grp.Ulift

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- Degree-zero small étale cohomology of the units sheaf is the additive group of global units. -/
theorem h0EtaleUnitsIsomorphicGlobalUnits (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})] :
    IsIsomorphic
      ((Sheaf.functorH S.smallEtaleTopology 0).obj (Etale.Small.unitsAddSheaf S))
      (AddCommGrpCat.of (Additive Γ(S, ⊤)ˣ)) := sorry

/-- The universe-lifted first small étale cohomology group of the units sheaf is isomorphic to
the Picard group. -/
theorem h1EtaleUnitsIsomorphicPicard (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})] :
    IsIsomorphic
      ((AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        ((Sheaf.functorH S.smallEtaleTopology 1).obj (Etale.Small.unitsAddSheaf S)))
      (AddCommGrpCat.of S.PicardGroup) := sorry

/-- Small étale and small Zariski cohomology of the additive structure sheaf agree in every
degree. -/
theorem etaleAdditiveCohomologyIsomorphicZariski (S : Scheme.{u}) (i : ℕ)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify S.smallZariskiTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallZariskiTopology AddCommGrpCat.{u})] :
    IsIsomorphic
      ((Sheaf.functorH S.smallEtaleTopology i).obj
        ((sheafCompose S.smallEtaleTopology (forget₂ RingCat AddCommGrpCat)).obj
          (Etale.Small.structureSheaf S)))
      ((Sheaf.functorH S.smallZariskiTopology i).obj
        ((sheafCompose S.smallZariskiTopology (forget₂ RingCat AddCommGrpCat)).obj
          (Zariski.Small.structureSheaf S))) := sorry

/-- Small étale and small Zariski cohomology of a quasi-coherent module agree in every degree. -/
theorem quasicoherentEtaleCohomologyIsomorphicZariski
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] (i : ℕ)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify S.smallZariskiTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallZariskiTopology AddCommGrpCat.{u})] :
    IsIsomorphic
      ((Sheaf.functorH S.smallEtaleTopology i).obj
        ((SheafOfModules.toSheaf (AssociatedModule.smallStructureSheaf .etale S)).obj
          (AssociatedModule.small .etale S F)))
      ((Sheaf.functorH S.smallZariskiTopology i).obj
        ((SheafOfModules.toSheaf (AssociatedModule.smallStructureSheaf .zariski S)).obj
          (AssociatedModule.small .zariski S F))) := sorry

end AlgebraicGeometry.Scheme

end
