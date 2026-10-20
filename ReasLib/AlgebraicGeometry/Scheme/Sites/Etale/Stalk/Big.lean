/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small
public import ReasLib.CategoryTheory.Sites.Point.Universe
public import Mathlib.CategoryTheory.Sites.Point.Map

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.GeometricPoint

/-- The stalk of a big étale sheaf at a geometric point of a scheme over the
base is the small étale stalk of its inverse image to that scheme. -/
noncomputable def bigEtaleStalk {S T : Scheme.{u}}
    (F : Sheaf (S.overGrothendieckTopology @Etale) (Type u))
    (t : GeometricPoint T) (f : T ⟶ S) : Type u :=
  Scheme.Etale.stalk t ((Scheme.Etale.SmallToBig.inverseImage f).obj F).obj

/-- The big étale stalk is the small étale stalk of the restricted sheaf. -/
theorem bigEtaleStalk_def {S T : Scheme.{u}}
    (F : Sheaf (S.overGrothendieckTopology @Etale) (Type u))
    (t : GeometricPoint T) (f : T ⟶ S) :
    bigEtaleStalk F t f =
      Scheme.Etale.stalk t ((Scheme.Etale.SmallToBig.inverseImage f).obj F).obj := sorry

/-- A geometric point of a scheme over the base determines a point of the big
étale site by mapping its small étale point along relocalization. -/
noncomputable def toBigEtalePoint {S T : Scheme.{u}}
    (t : GeometricPoint T) (f : T ⟶ S) :
    GrothendieckTopology.Point.{u} (S.overGrothendieckTopology @Etale) :=
  (toSmallEtalePoint t).map (Scheme.Etale.SmallToBig.relocalizationFunctor f)
    (S.overGrothendieckTopology @Etale)

/-- The sheaf fiber at a mapped big étale point is canonically isomorphic to
the stalk of the restriction at the original geometric point. -/
noncomputable def toBigEtalePointStalkIso {S T : Scheme.{u}}
    (F : Sheaf (S.overGrothendieckTopology @Etale) (Type u))
    (t : GeometricPoint T) (f : T ⟶ S) :
    (toBigEtalePoint t f).sheafFiber.obj F ≅ bigEtaleStalk F t f :=
  ((toSmallEtalePoint t).sheafFiberMapIso
    (Scheme.Etale.SmallToBig.relocalizationFunctor f)
    (S.overGrothendieckTopology @Etale) (Type u)).app F

end AlgebraicGeometry.Scheme.GeometricPoint
