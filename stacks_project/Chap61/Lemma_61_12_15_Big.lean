/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.Big

/-!
# Big pro-étale sheaf functors

Typed compatibility checks for the chosen big pro-étale slice constructions.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.ChosenBigProetaleSite

variable {X : ChosenBigProetaleSite.{u, v}} {S T : X.carrier} (f : T ⟶ S)

#check (AlgebraicGeometry.ChosenBigProetaleSite.Big.mapPullbackAdjunction f :
  Big.map f ⊣ Big.pullback f)

#check (AlgebraicGeometry.ChosenBigProetaleSite.Big.inverseImage.{u, v, w} f :
  Sheaf (bigTopology X S) (Type w) ⥤ Sheaf (bigTopology X T) (Type w))

#check (AlgebraicGeometry.ChosenBigProetaleSite.Big.directImage.{u, v, w} f :
  Sheaf (bigTopology X T) (Type w) ⥤ Sheaf (bigTopology X S) (Type w))

#check (AlgebraicGeometry.ChosenBigProetaleSite.Big.morphismOfTopoi.{u, v, w} f :
  MorphismOfTopoiIn.{max u v, max u v, u, u, w} (bigTopology X S) (bigTopology X T))

#check (AlgebraicGeometry.ChosenBigProetaleSite.Big.lowerShriekAdjunction.{u, v, w} f :
  Big.lowerShriek.{u, v, w} f ⊣ Big.inverseImage.{u, v, max u v w} f)

end AlgebraicGeometry.ChosenBigProetaleSite
