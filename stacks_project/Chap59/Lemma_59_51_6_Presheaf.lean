/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.DirectImage

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open AlgebraicGeometry
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Compatibility access to the canonical étale cohomology presheaf. -/
#check
  (AlgebraicGeometry.Scheme.etalePullbackCohomologyPresheaf :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (p : ℕ),
      Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u})

end AlgebraicGeometry.Scheme
