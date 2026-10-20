/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Over
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.ChosenPresentation
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable

/-! Sheafified Yoneda constructions for the chosen big fppf site. -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open CategoryTheory.Functor
open AlgebraicGeometry.ChosenBigFppfSite
open Opposite
noncomputable section
universe u v
namespace AlgebraicGeometry
namespace ChosenBigFppfSite


/-- The sheaf on `(Sch/S)_fppf` associated to a scheme over the image of `S`,
obtained by sheafifying Hom-spaces in the slice and lifting to
`Type (max u v)`. -/
def sheafifyYoneda {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))] :
    Over (𝒮.toScheme.obj S) ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v)) where
  obj Y :=
    (presheafToSheaf (𝒮.bigTopology S) (Type (max u v))).obj
      ((Over.post 𝒮.toScheme).op ⋙ yoneda.obj Y ⋙ uliftFunctor.{v})
  map {Y Z} f :=
    (presheafToSheaf (𝒮.bigTopology S) (Type (max u v))).map
      (whiskerRight (whiskerLeft (Over.post 𝒮.toScheme).op (yoneda.map f))
        uliftFunctor.{v})
  map_id := by
    intro Y
    simp only [CategoryTheory.Functor.map_id]
    exact (presheafToSheaf (𝒮.bigTopology S) (Type (max u v))).map_id _
  map_comp := by
    intro Y Z W f g
    simp only [CategoryTheory.Functor.map_comp, whiskerLeft_comp, whiskerRight_comp]
    exact (presheafToSheaf (𝒮.bigTopology S) (Type (max u v))).map_comp _ _

/-- `sheafifyYoneda.obj Y` is the sheafification of the `ULift` of Hom-spaces
in the slice along `Over.post 𝒮.toScheme`. -/
theorem sheafifyYoneda_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (Y : Over (𝒮.toScheme.obj S)) :
    sheafifyYoneda.obj Y =
      (presheafToSheaf (𝒮.bigTopology S) (Type (max u v))).obj
        ((Over.post 𝒮.toScheme).op ⋙ yoneda.obj Y ⋙ uliftFunctor.{v}) := by rfl

/-- Presheaf comparison from slice Yoneda of a site object to `uliftYoneda`. -/
def toUliftYoneda {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    (U : 𝒮.bigSite S) :
    ((Over.post 𝒮.toScheme).op ⋙ yoneda.obj ((Over.post 𝒮.toScheme).obj U) ⋙
        uliftFunctor.{v}) ⟶
      uliftYoneda.{max u v}.obj U where
  app W :=
    ↾fun f ↦
      ULift.up.{max u v, u}
        (Over.homMk (𝒮.fullyFaithful.preimage f.down.left) (by
          apply 𝒮.fullyFaithful.map_injective
          rw [CategoryTheory.Functor.map_comp, 𝒮.fullyFaithful.map_preimage]
          have h := f.down.w
          dsimp [Over.post] at h
          exact h))
  naturality := by
    intro A B f
    ext t
    apply ULift.ext
    apply Over.OverMorphism.ext
    apply 𝒮.fullyFaithful.map_injective
    change 𝒮.toScheme.map (𝒮.fullyFaithful.preimage (𝒮.toScheme.map f.unop.left ≫ t.down.left)) =
      𝒮.toScheme.map (f.unop.left ≫ 𝒮.fullyFaithful.preimage t.down.left)
    rw [CategoryTheory.Functor.map_comp, 𝒮.fullyFaithful.map_preimage,
      𝒮.fullyFaithful.map_preimage]

/-- Comparison from the sheafified slice Yoneda of a site object to its
sheafified representable, using full faithfulness of `𝒮.toScheme`. -/
def toSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))] (U : 𝒮.bigSite S) :
    sheafifyYoneda.obj ((Over.post 𝒮.toScheme).obj U) ⟶
      (𝒮.bigTopology S).sheafifiedRepresentable U :=
  (presheafToSheaf (𝒮.bigTopology S) (Type (max u v))).map (toUliftYoneda U)

/-- `toSheafifiedRepresentable U` is the sheafification of `toUliftYoneda U`. -/
theorem toSheafifiedRepresentable_spec {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))] (U : 𝒮.bigSite S) :
    toSheafifiedRepresentable U =
      (presheafToSheaf (𝒮.bigTopology S) (Type (max u v))).map
        (toUliftYoneda U) := by rfl


end ChosenBigFppfSite
end AlgebraicGeometry
