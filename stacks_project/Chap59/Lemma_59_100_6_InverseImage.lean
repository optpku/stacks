/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.EtaleInverseImage

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.FppfEtale

/-- Every étale covering of schemes is an fppf covering. -/
theorem etale_le_fppf : etaleTopology.{u} ≤ fppfTopology.{u} :=
  Precoverage.toGrothendieck_mono etalePrecoverage_le_fppfPrecoverage

end AlgebraicGeometry.Scheme.FppfEtale

#check (AlgebraicGeometry.Scheme.FppfEtale.aInverseAb :
  (X : Scheme.{u}) → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
    Sheaf (fppfTopology.over X) AddCommGrpCat.{u + 1})

end
