/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.InverseImage.Exact

/-! # Exactness of inverse image on small étale sites -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/- Lemma 66.19.9 (1): inverse image on abelian sheaves is exact. -/
#check (AlgebraicGeometry.AlgebraicSpace.smallEtaleInverseImage_exact_addCommGrp f :
  exactFunctor (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
      (sheafInverseImage AddCommGrpCat.{u + 1} f))

/- Lemma 66.19.9 (2): inverse image on sheaves of sets is exact. -/
#check (AlgebraicGeometry.AlgebraicSpace.smallEtaleInverseImage_exact_type f :
  exactFunctor (Sheaf (smallEtaleTopology Y) (Type (u + 1)))
      (Sheaf (smallEtaleTopology X) (Type (u + 1)))
      (smallEtaleMorphismOfTopoi f).inverseImage)
