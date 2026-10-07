module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Submersive
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.GeometricallyConnected
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Global sections on the small étale site

Global étale objects, restriction of set-valued sections, and the open locus
where two global sections agree.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The identity object of the small étale site of a scheme. -/
abbrev globalEtale (X : Scheme.{u}) : X.Etale :=
  MorphismProperty.Over.mk _ (𝟙 X) inferInstance

/-- Base change of the identity étale object along a scheme morphism is isomorphic to
the identity étale object of its domain. -/
def globalEtalePullbackIso {S T : Scheme.{u}} (f : T ⟶ S) :
    (smallEtalePullback f).obj (globalEtale S) ≅ globalEtale T :=
  let e : pullback (𝟙 S) f ≅ T := asIso (pullback.snd (𝟙 S) f)
  MorphismProperty.Over.isoMk e (by
    change pullback.snd (𝟙 S) f = pullback.snd (𝟙 S) f
    rfl)

/-- Restriction of a global section along a scheme morphism, obtained from the
unit of the inverse-image/direct-image adjunction. -/
def restrictGlobalSection {S T : Scheme.{u}} (f : T ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (σ : F.obj.obj (op (globalEtale S))) :
    (((smallEtalePullback f).sheafPullback (Type (u + 1))
        S.smallEtaleTopology T.smallEtaleTopology).obj F).obj.obj
      (op (globalEtale T)) :=
  (((smallEtalePullback f).sheafPullback (Type (u + 1))
        S.smallEtaleTopology T.smallEtaleTopology).obj F).obj.map
    (op (globalEtalePullbackIso f).inv)
    (((sheafToPresheaf S.smallEtaleTopology (Type (u + 1))).map
        ((smallEtalePullback_sheafAdjunction f (Type (u + 1))).unit.app F)).app
      (op (globalEtale S)) σ)

/-- Two global sections of a set-valued sheaf on the small étale site agree after
pullback along exactly the morphisms factoring through a unique open subscheme. -/
theorem existsUnique_open_of_eq_sections {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (s t : F.obj.obj (op (globalEtale S))) :
    ∃! W : S.Opens,
      ∀ {T : Scheme.{u}} (f : T ⟶ S),
        (∃ g : T ⟶ W, g ≫ W.ι = f) ↔
          restrictGlobalSection f F s = restrictGlobalSection f F t := sorry

/-- Restriction of global étale sections along a submersive scheme morphism with
geometrically connected fibres is bijective. -/
theorem restrictGlobalSection_bijective_of_submersive_geometricallyConnected
    {X S : Scheme.{u}} (f : X ⟶ S) [Submersive f]
    (h_geomConnected : ∀ y : S, GeometricallyConnected (f.fiberToSpecResidueField y))
    [HasWeakSheafify S.smallEtaleTopology (Type (u + 1))]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [∀ P : S.Etaleᵒᵖ ⥤ Type (u + 1),
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    Function.Bijective (restrictGlobalSection f F) := sorry

/-- Restriction of global étale sections along a flat quasi-compact scheme morphism
with geometrically connected fibres is bijective. -/
theorem restrictGlobalSection_bijective_of_flat_geometricallyConnected
    {T S : Scheme.{u}} (f : T ⟶ S) [Flat f] [QuasiCompact f]
    [GeometricallyConnected f]
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    Function.Bijective (restrictGlobalSection f F) := sorry

/-- Global étale sections are equivalent to their pullbacks along a submersive scheme
morphism with geometrically connected fibres, with forward map `restrictGlobalSection`. -/
noncomputable def restrictGlobalSectionEquiv_of_submersive_geometricallyConnected
    {X S : Scheme.{u}} (f : X ⟶ S) [Submersive f]
    (h_geomConnected : ∀ y : S, GeometricallyConnected (f.fiberToSpecResidueField y))
    [HasWeakSheafify S.smallEtaleTopology (Type (u + 1))]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [∀ P : S.Etaleᵒᵖ ⥤ Type (u + 1),
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    F.obj.obj (op (globalEtale S)) ≃
      (((smallEtalePullback f).sheafPullback (Type (u + 1))
          S.smallEtaleTopology X.smallEtaleTopology).obj F).obj.obj
        (op (globalEtale X)) :=
  Equiv.ofBijective (restrictGlobalSection f F)
    (restrictGlobalSection_bijective_of_submersive_geometricallyConnected f
      h_geomConnected F)

/-- The equivalence of global étale sections along a submersive morphism with
geometrically connected fibres applies as the canonical restriction map. -/
theorem restrictGlobalSectionEquiv_of_submersive_geometricallyConnected_apply
    {X S : Scheme.{u}} (f : X ⟶ S) [Submersive f]
    (h_geomConnected : ∀ y : S, GeometricallyConnected (f.fiberToSpecResidueField y))
    [HasWeakSheafify S.smallEtaleTopology (Type (u + 1))]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [∀ P : S.Etaleᵒᵖ ⥤ Type (u + 1),
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (σ : F.obj.obj (op (globalEtale S))) :
    restrictGlobalSectionEquiv_of_submersive_geometricallyConnected f
        h_geomConnected F σ =
      restrictGlobalSection f F σ := sorry

end AlgebraicGeometry.Scheme.Etale

end
