module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.FMap.Linear
public import ReasLib.Topology.OpenCover.Refinement
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module-linear Cech maps for bundled open covers

This leaf is the short-parameter interface to `ModuleCech.FMap.Linear`.  A source cover `𝒰`
and a target cover `𝒱` carry their covering proofs, while a refinement
`𝒱.comap f.hom.base.hom ⟶ 𝒰` carries both the selected index map and all containment conditions.
The resulting maps therefore require no separate index types, families, supremum equalities, or
raw refinement predicate.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCech.FMap.Linear.Bundled

variable {X Y : RingedSpace.{u}}

/-- A bundled refinement of `𝒰` by the inverse-image cover of `𝒱` gives the raw refinement
predicate used by the unbundled Cech-map core. -/
@[stacks 01FD "bundled refinement underlying a Cech f-map"]
theorem toIsRefinement (f : X ⟶ Y)
    (𝒰 : OpenCover.{u} X.carrier) (𝒱 : OpenCover.{u} Y.carrier)
    (r : OpenCover.Refinement (𝒱.comap f.hom.base.hom) 𝒰) :
    IsRefinement (fun j ↦ preimageOpen f (𝒱 j)) 𝒰 r.indexMap := sorry

/-- The module-valued Cech source associated with a bundled cover of `Y`. -/
@[stacks 01FD "bundled module-linear Cech f-map source"]
abbrev sourceComplex (𝒱 : OpenCover.{u} Y.carrier) (G : Y.Modules) :=
  Linear.sourceComplex 𝒱 𝒱.isCover.iSup_eq_top G

/-- The module-valued Cech target associated with a bundled cover of `X`, with scalars
restricted to `Γ(Y, 𝒪_Y)`. -/
@[stacks 01FD "bundled module-linear Cech f-map target"]
abbrev targetComplex (f : X ⟶ Y) (𝒰 : OpenCover.{u} X.carrier)
    (F : X.Modules) :=
  Linear.targetComplex f 𝒰 𝒰.isCover.iSup_eq_top F

/-- The concrete `Γ(Y, 𝒪_Y)`-linear Cech map attached to bundled covers and a selected
refinement of the inverse-image cover. -/
@[stacks 01FD "bundled module-linear Cech complex map of an f-map"]
noncomputable abbrev complexMap
    (f : X ⟶ Y) (𝒰 : OpenCover.{u} X.carrier) (𝒱 : OpenCover.{u} Y.carrier)
    (r : OpenCover.Refinement (𝒱.comap f.hom.base.hom) 𝒰)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) :
    sourceComplex 𝒱 G ⟶ targetComplex f 𝒰 F :=
  Linear.complexMap f 𝒰 𝒰.isCover.iSup_eq_top 𝒱 𝒱.isCover.iSup_eq_top
    r.indexMap (toIsRefinement f 𝒰 𝒱 r) φ

/-- The bounded-below derived source associated with a bundled cover of `Y`. -/
@[stacks 01FD "bundled bounded-below module-linear Cech f-map source"]
abbrev derivedSource (𝒱 : OpenCover.{u} Y.carrier) (G : Y.Modules) :=
  Linear.derivedSource 𝒱 𝒱.isCover.iSup_eq_top G

/-- The bounded-below derived target associated with a bundled cover of `X`, with scalars
restricted to `Γ(Y, 𝒪_Y)`. -/
@[stacks 01FD "bundled bounded-below module-linear Cech f-map target"]
abbrev derivedTarget (f : X ⟶ Y) (𝒰 : OpenCover.{u} X.carrier)
    (F : X.Modules) :=
  Linear.derivedTarget f 𝒰 𝒰.isCover.iSup_eq_top F

/-- The target Cech complex as a coefficient functor in `F`.  Keeping this functor explicit makes
the target comparison in a change-of-space square genuinely natural in the module coefficient. -/
@[stacks 01FD "bundled target Cech complex functor"]
abbrev targetSource (f : X ⟶ Y) (𝒰 : OpenCover.{u} X.carrier) :
    X.Modules ⥤ CochainComplex (ModuleCat (globalSectionsRing Y)) ℕ :=
  ModuleCech.complex (⊤ : Opens X.carrier)
      (Opens.Cover.overFamily ⊤ 𝒰 𝒰.isCover.iSup_eq_top) ⋙
    (moduleSectionsRestrictionFunctor f ⊤).mapHomologicalComplex
      (ComplexShape.up ℕ)

/-- The bounded-below derived target Cech functor over `Γ(Y, 𝒪_Y)`. -/
@[stacks 01FD "bundled derived target Cech functor"]
abbrev derivedTargetFunctor (f : X ⟶ Y) (𝒰 : OpenCover.{u} X.carrier) :
    X.Modules ⥤ DerivedCategory.Plus (ModuleCat (globalSectionsRing Y)) :=
  targetSource f 𝒰 ⋙
    CochainComplex.Plus.extendNat (ModuleCat (globalSectionsRing Y)) ⋙
    DerivedCategory.Plus.Q

@[simp]
theorem derivedTargetFunctor_obj (f : X ⟶ Y) (𝒰 : OpenCover.{u} X.carrier)
    (F : X.Modules) :
    (derivedTargetFunctor f 𝒰).obj F = derivedTarget f 𝒰 F := rfl

/-- The `D⁺(ModuleCat (globalSectionsRing Y))` map attached to bundled covers and an
inverse-image refinement. -/
@[stacks 01FD "bundled bounded-below module-linear Cech map of an f-map"]
noncomputable abbrev derivedMap
    (f : X ⟶ Y) (𝒰 : OpenCover.{u} X.carrier) (𝒱 : OpenCover.{u} Y.carrier)
    (r : OpenCover.Refinement (𝒱.comap f.hom.base.hom) 𝒰)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) :
    derivedSource 𝒱 G ⟶ derivedTarget f 𝒰 F :=
  Linear.derivedMap f 𝒰 𝒰.isCover.iSup_eq_top 𝒱 𝒱.isCover.iSup_eq_top
    r.indexMap (toIsRefinement f 𝒰 𝒱 r) φ

/-- Degree-`p` module-valued Cech cohomology associated with a bundled cover of `Y`. -/
@[stacks 01FD "bundled module-linear Cech cohomology f-map source"]
abbrev cohomologySource (𝒱 : OpenCover.{u} Y.carrier)
    (G : Y.Modules) (p : ℕ) :=
  Linear.cohomologySource 𝒱 𝒱.isCover.iSup_eq_top G p

/-- Degree-`p` module-valued Cech cohomology associated with a bundled cover of `X`, after
restriction to `Γ(Y, 𝒪_Y)`. -/
@[stacks 01FD "bundled module-linear Cech cohomology f-map target"]
abbrev cohomologyTarget (f : X ⟶ Y) (𝒰 : OpenCover.{u} X.carrier)
    (F : X.Modules) (p : ℕ) :=
  Linear.cohomologyTarget f 𝒰 𝒰.isCover.iSup_eq_top F p

/-- The `Γ(Y, 𝒪_Y)`-linear Cech cohomology map attached to bundled covers and an
inverse-image refinement. -/
@[stacks 01FD "bundled module-linear Cech cohomology map of an f-map"]
noncomputable abbrev cohomologyMap
    (f : X ⟶ Y) (𝒰 : OpenCover.{u} X.carrier) (𝒱 : OpenCover.{u} Y.carrier)
    (r : OpenCover.Refinement (𝒱.comap f.hom.base.hom) 𝒰)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) (p : ℕ) :
    cohomologySource 𝒱 G p ⟶ cohomologyTarget f 𝒰 F p :=
  Linear.cohomologyMap f 𝒰 𝒰.isCover.iSup_eq_top 𝒱 𝒱.isCover.iSup_eq_top
    r.indexMap (toIsRefinement f 𝒰 𝒱 r) φ p

end AlgebraicGeometry.RingedSpace.ModuleCech.FMap.Linear.Bundled
