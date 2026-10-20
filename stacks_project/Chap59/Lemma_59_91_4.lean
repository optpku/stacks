/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.GeometricFiberSections
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

/- Lemma 59.91.4: if `f : X ⟶ S` is proper and `s̄` is a geometric point of `S`,
then for every sheaf of sets `F` on `X_étale` the canonical comparison
`(f_* F)_{s̄} ⟶ Γ(X_{s̄}, F|_{X_{s̄}})` is bijective, where `X_{s̄}` is the
geometric fibre `pullback f s.hom`. -/
@[stacks 0A3T] #check
  (AlgebraicGeometry.Scheme.Hom.etalePushforwardStalk_bijective_of_isProper :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s : GeometricPoint S)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    [HasWeakSheafify (pullback f s.hom).smallEtaleTopology (Type u)]
    [∀ P : X.Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback (pullback.fst f s.hom)).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology (Type u)),
      Function.Bijective
        (AlgebraicGeometry.Scheme.Hom.etalePushforwardStalkToGeometricFiberSections f s F))

end
