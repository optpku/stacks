/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Descent along presentations of algebraic spaces

A morphism from a presenting scheme that equalizes the relation descends by sheaf
amalgamation along the atlas.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Presentation

private def homDescLocalFamily {S : Scheme.{u}} {X : AlgebraicSpace S}
    (P : Presentation X) {Y : AlgebraicSpace S} (g : ofOver P.U ⟶ Y)
    {V : (Over S)ᵒᵖ} (x : X.functorOfPoints.obj V) :
    Presieve.FamilyOfElements Y.functorOfPoints (Presheaf.imageSieve P.atlas x).arrows :=
  fun W f hf => g.app (op W) (Presheaf.localPreimage P.atlas x f hf)

private theorem homDescLocalFamily_compatible {S : Scheme.{u}} {X : AlgebraicSpace S}
    (P : Presentation X) {Y : AlgebraicSpace S} (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g)
    {V : (Over S)ᵒᵖ} (x : X.functorOfPoints.obj V) :
    (homDescLocalFamily P g x).Compatible :=
  sorry

private def homDescApp {S : Scheme.{u}} {X : AlgebraicSpace S}
    (P : Presentation X) {Y : AlgebraicSpace S} (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g)
    (V : (Over S)ᵒᵖ) (x : X.functorOfPoints.obj V) : Y.functorOfPoints.obj V :=
  let comparison : Scheme.etaleTopology.{u} ≤ Scheme.fppfTopology :=
    Scheme.grothendieckTopology_monotone (fun _ _ i _ ↦
      ⟨inferInstanceAs (AlgebraicGeometry.Flat i),
        inferInstanceAs (AlgebraicGeometry.LocallyOfFinitePresentation i)⟩)
  let covering : Presheaf.imageSieve P.atlas x ∈ (Scheme.fppfTopology.over S) V.unop :=
    comparison _ (P.atlas_locallySurjective.imageSieve_mem x)
  let sheaf := (isSheaf_iff_isSheaf_of_type _ _).1 Y.isSheaf _ covering
  sheaf.amalgamate (homDescLocalFamily P g x) (homDescLocalFamily_compatible P g h x)

private theorem homDescApp_naturality {S : Scheme.{u}} {X : AlgebraicSpace S}
    (P : Presentation X) {Y : AlgebraicSpace S} (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g)
    {V W : (Over S)ᵒᵖ} (f : V ⟶ W) :
    X.functorOfPoints.map f ≫ TypeCat.ofHom (homDescApp P g h W) =
      TypeCat.ofHom (homDescApp P g h V) ≫ Y.functorOfPoints.map f :=
  sorry

/-- A morphism from a presenting scheme that equalizes the relation descends uniquely
to a morphism of algebraic spaces. -/
@[no_expose] def homDesc {S : Scheme.{u}} {X : AlgebraicSpace S} (P : Presentation X)
    {Y : AlgebraicSpace S} (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g) : X ⟶ Y where
  app V := TypeCat.ofHom (homDescApp P g h V)
  naturality := fun _ _ f => homDescApp_naturality P g h f

/-- Precomposing a descended morphism with the atlas recovers the given morphism
from the presenting scheme. -/
theorem homDesc_comp_atlas {S : Scheme.{u}} {X : AlgebraicSpace S} (P : Presentation X)
    {Y : AlgebraicSpace S} (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g) :
    P.atlas ≫ homDesc P g h = (g : yoneda.obj P.U ⟶ Y.functorOfPoints) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Presentation
