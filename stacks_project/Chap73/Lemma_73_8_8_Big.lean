/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Over.Topos
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.Site
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Big ph sheaf functors on algebraic spaces

Postcomposition and pullback on slice categories induce the big ph sheaf
functors. The big ph morphism is the canonical morphism for the slice topology.
-/

@[expose] public section

open CategoryTheory
open Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Ph.Big

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Postcomposition on the big ph slice categories. -/
abbrev map (f : Y ⟶ X) : Over Y ⥤ Over X :=
  CategoryTheory.Over.Site.mapFunctor f

/-- Sheaves of types in universe `u + 1` on the big ph site admit weak
sheafification. -/
instance bigPhSite_hasWeakSheafify (X : AlgebraicSpace S) :
    HasWeakSheafify (bigPhSite X) (Type (u + 1)) :=
  inferInstance

/-- Inverse image on big ph sheaves is restriction along postcomposition. -/
abbrev inverseImage (f : Y ⟶ X) :
    Sheaf (bigPhSite X) (Type (u + 1)) ⥤ Sheaf (bigPhSite Y) (Type (u + 1)) :=
  CategoryTheory.Over.Site.inverseImage (phTopology S) f

/-- The morphism of big ph topoi induced by a morphism of algebraic spaces. -/
abbrev morphismOfTopoi (f : Y ⟶ X) :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (bigPhSite X) (bigPhSite Y) :=
  CategoryTheory.Over.Site.morphismOfTopoi (phTopology S) f

variable (f : Y ⟶ X)

#check (CategoryTheory.Over.Site.mapFunctor f : Over Y ⥤ Over X)

#check (CategoryTheory.Over.Site.pullbackFunctor f : Over X ⥤ Over Y)

#check (CategoryTheory.Over.Site.inverseImage (phTopology S) f :
  Sheaf (bigPhSite X) (Type (u + 1)) ⥤ Sheaf (bigPhSite Y) (Type (u + 1)))

#check (CategoryTheory.Over.Site.directImage (phTopology S) f :
  Sheaf (bigPhSite Y) (Type (u + 1)) ⥤ Sheaf (bigPhSite X) (Type (u + 1)))

#check (CategoryTheory.Over.Site.lowerShriek (phTopology S) f :
  Sheaf (bigPhSite Y) (Type (u + 1)) ⥤ Sheaf (bigPhSite X) (Type (u + 1)))

#check (CategoryTheory.Over.Site.InverseImage.objIso (phTopology S) f :
  ∀ (G : Sheaf (bigPhSite X) (Type (u + 1))) (U : Over Y),
    ((CategoryTheory.Over.Site.inverseImage (phTopology S) f).obj G).obj.obj (op U) ≅
      G.obj.obj (op ((Over.map f).obj U)))

#check (CategoryTheory.Over.Site.Morphism.inverseImage.{u + 1, u + 1, u + 1} (phTopology S) f :
  (morphismOfTopoi f)⁻¹ =
    (CategoryTheory.Over.Site.inverseImage (phTopology S) f :
      Sheaf (bigPhSite X) (Type (u + 1)) ⥤ Sheaf (bigPhSite Y) (Type (u + 1))))

#check (CategoryTheory.Over.Site.Morphism.pushforward.{u + 1, u + 1, u + 1} (phTopology S) f :
  (morphismOfTopoi f).pushforward =
    (CategoryTheory.Over.Site.directImage (phTopology S) f :
      Sheaf (bigPhSite Y) (Type (u + 1)) ⥤ Sheaf (bigPhSite X) (Type (u + 1))))

end AlgebraicGeometry.AlgebraicSpace.Ph.Big
