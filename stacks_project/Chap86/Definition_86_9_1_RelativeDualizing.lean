/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap70.Lemma_70_14_4_Pullback
public import stacks_project.Chap75.Lemma_75_11_2_Pushforward
public import stacks_project.Chap75.Lemma_75_26_6_Pullback
public import stacks_project.Chap76.Lemma_76_52_4_Relative
public import stacks_project.Chap86.«86_3_2_1_Pushforward»

/-!
# Relative dualizing complexes for proper flat morphisms of algebraic spaces

A relative dualizing complex for a proper, flat, finitely presented morphism of algebraic
spaces is a pair `(ω, τ)` consisting of a `Y`-perfect object of `D(𝒪_X)` and a trace
`Rf_* ω ⟶ 𝒪_Y` whose cartesian base change to any affine algebraic space recovers the
twisted-inverse pair `(a'(𝒪_{Y'}), Tr)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structure sheaf of an algebraic space, placed in degree zero as an object of
`D(𝒪_X)`. -/
noncomputable def derivedStructureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ModuleDerived X :=
  (DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj
    (SheafOfModules.unit (structureSheaf X) : X.Modules)

/-- The derived structure sheaf is the unit `𝒪_X`-module placed in degree zero. -/
theorem derivedStructureSheaf_obj {S : Scheme.{u}} (X : AlgebraicSpace S) :
    derivedStructureSheaf X =
      (DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj
        (SheafOfModules.unit (structureSheaf X) : X.Modules) :=
  sorry

/-- The structure sheaf in degree zero has quasi-coherent cohomology. -/
theorem derivedStructureSheaf_mem {S : Scheme.{u}} (X : AlgebraicSpace S) :
    derivedQuasiCoherentModuleProperty X (derivedStructureSheaf X) :=
  sorry

/-- The twisted inverse image `a(𝒪_Y)` of the derived structure sheaf, as an object of
`D(𝒪_X)`. -/
noncomputable def twistedInverseComplex {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) :
    ModuleDerived X :=
  (inclusion X).obj
    (a.obj ⟨derivedStructureSheaf Y, derivedStructureSheaf_mem Y⟩)

/-- The twisted inverse image is the included value of `a` on the derived structure sheaf. -/
theorem twistedInverseComplex_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) :
    twistedInverseComplex f a =
      (inclusion X).obj
        (a.obj ⟨derivedStructureSheaf Y, derivedStructureSheaf_mem Y⟩) :=
  sorry

/-- The trace `Tr_{f, 𝒪_Y}` is the included counit of `Rf_* ⊣ a` at the derived structure
sheaf. -/
noncomputable def twistedInverseTrace {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a) :
    (moduleDerivedPushforward f).obj (twistedInverseComplex f a) ⟶
      derivedStructureSheaf Y :=
  let OY : DerivedQCoh Y := ⟨derivedStructureSheaf Y, derivedStructureSheaf_mem Y⟩
  (pushforwardCohomologyIn.inclusionIso f).inv.app (a.obj OY) ≫
    (inclusion Y).map (adj.counit.app OY)

/-- The twisted-inverse trace is the included counit of the chosen `D_QCoh` adjunction. -/
theorem twistedInverseTrace_counit {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a) :
    twistedInverseTrace f a adj =
      (pushforwardCohomologyIn.inclusionIso f).inv.app
          (a.obj ⟨derivedStructureSheaf Y, derivedStructureSheaf_mem Y⟩) ≫
        (inclusion Y).map
          (adj.counit.app ⟨derivedStructureSheaf Y, derivedStructureSheaf_mem Y⟩) :=
  sorry

/-- The canonical comparison `L(g)^* 𝒪_Y ⟶ 𝒪_{Y'}` from derived pullback of the structure
sheaf to the structure sheaf of the source. -/
noncomputable def derivedStructureSheafPullback {S : Scheme.{u}} {Y' Y : AlgebraicSpace S}
    (g : Y' ⟶ Y) :
    (ModuleDerived.pullback g).obj (derivedStructureSheaf Y) ⟶ derivedStructureSheaf Y' :=
  ModuleDerived.singlePullbackComparison g
      (SheafOfModules.unit (structureSheaf Y) : Y.Modules) (0 : ℤ) ≫
    (DerivedCategory.singleFunctor (Modules Y') (0 : ℤ)).map (pullbackObjUnitToUnit g)

/-- Derived pullback of the structure sheaf compares with the structure sheaf of the source
through the single-object derived comparison and the underived unit comparison. -/
theorem derivedStructureSheafPullback_eq {S : Scheme.{u}} {Y' Y : AlgebraicSpace S}
    (g : Y' ⟶ Y) :
    derivedStructureSheafPullback g =
      ModuleDerived.singlePullbackComparison g
          (SheafOfModules.unit (structureSheaf Y) : Y.Modules) (0 : ℤ) ≫
        (DerivedCategory.singleFunctor (Modules Y') (0 : ℤ)).map
          (pullbackObjUnitToUnit g) :=
  sorry

/-- The pulled-back trace `L(g)^* τ : L(g)^* Rf_* ω ⟶ 𝒪_{Y'}`. -/
noncomputable def pulledTrace {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y)
    (g : Y' ⟶ Y) {ω : ModuleDerived X}
    (τ : (moduleDerivedPushforward f).obj ω ⟶ derivedStructureSheaf Y) :
    (ModuleDerived.pullback g).obj ((moduleDerivedPushforward f).obj ω) ⟶
      derivedStructureSheaf Y' :=
  (ModuleDerived.pullback g).map τ ≫ derivedStructureSheafPullback g

/-- The pulled-back trace is derived pullback of `τ` followed by the structure-sheaf
comparison. -/
theorem pulledTrace_eq {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y)
    (g : Y' ⟶ Y) {ω : ModuleDerived X}
    (τ : (moduleDerivedPushforward f).obj ω ⟶ derivedStructureSheaf Y) :
    pulledTrace f g τ =
      (ModuleDerived.pullback g).map τ ≫ derivedStructureSheafPullback g :=
  sorry

namespace ModuleDerived

/-- The canonical derived identification of the two paths around a cartesian square,
built from composition comparisons and the square equality `g' ≫ f = f' ≫ g`. -/
noncomputable def pullbackCartesianIso {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    [IsIso (pullbackCompComparison f' g)] [IsIso (pullbackCompComparison g' f)] :
    pullback g ⋙ pullback f' ≅ pullback f ⋙ pullback g' :=
  asIso (pullbackCompComparison f' g) ≪≫
    eqToIso (congrArg pullback sq.w.symm) ≪≫
    (asIso (pullbackCompComparison g' f)).symm

/-- The cartesian derived identification is the composition comparison along `f' ≫ g`,
the equality `sq.w`, and the inverse composition comparison along `g' ≫ f`. -/
theorem pullbackCartesianIso_hom {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    [IsIso (pullbackCompComparison f' g)] [IsIso (pullbackCompComparison g' f)] :
    (pullbackCartesianIso g' f' f g sq).hom =
      pullbackCompComparison f' g ≫
        eqToHom (congrArg pullback sq.w.symm) ≫ inv (pullbackCompComparison g' f) :=
  sorry

end ModuleDerived

/-- The derived base-change mate `β : L(g)^* Rf_* ω ⟶ Rf'_* L(g')^* ω` of a cartesian
square. -/
noncomputable def baseChangeMate {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
    (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (ω : ModuleDerived X) :
    (ModuleDerived.pullback g).obj ((moduleDerivedPushforward f).obj ω) ⟶
      (moduleDerivedPushforward f').obj ((ModuleDerived.pullback g').obj ω) :=
  (CategoryTheory.DerivedBaseChange.map adj_f adj_f'
      (ModuleDerived.pullbackCartesianIso g' f' f g sq)).app ω

/-- The base-change mate is the component of the categorical right mate at `ω`. -/
theorem baseChangeMate_eq {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
    (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (ω : ModuleDerived X) :
    baseChangeMate g' f' f g sq adj_f adj_f' ω =
      (CategoryTheory.DerivedBaseChange.map adj_f adj_f'
          (ModuleDerived.pullbackCartesianIso g' f' f g sq)).app ω :=
  sorry

/-- The cartesian base-changed trace `Lg^* τ : Rf'_* L(g')^* ω ⟶ 𝒪_{Y'}`, obtained by
transporting `L(g)^* τ` across the inverse of the base-change mate. -/
noncomputable def baseChangedTrace {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
    (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    {ω : ModuleDerived X}
    [IsIso (baseChangeMate g' f' f g sq adj_f adj_f' ω)]
    (τ : (moduleDerivedPushforward f).obj ω ⟶ derivedStructureSheaf Y) :
    (moduleDerivedPushforward f').obj ((ModuleDerived.pullback g').obj ω) ⟶
      derivedStructureSheaf Y' :=
  inv (baseChangeMate g' f' f g sq adj_f adj_f' ω) ≫ pulledTrace f g τ

/-- The base-changed trace is the inverse mate followed by the pulled-back trace. -/
theorem baseChangedTrace_eq {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
    (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    {ω : ModuleDerived X}
    [IsIso (baseChangeMate g' f' f g sq adj_f adj_f' ω)]
    (τ : (moduleDerivedPushforward f).obj ω ⟶ derivedStructureSheaf Y) :
    baseChangedTrace g' f' f g sq adj_f adj_f' τ =
      inv (baseChangeMate g' f' f g sq adj_f adj_f' ω) ≫ pulledTrace f g τ :=
  sorry

/-- Postcomposition with the base-changed trace, as a map on Hom-spaces
`Hom(M', L(g')^* ω) → Hom(Rf'_* M', 𝒪_{Y'})`. -/
noncomputable def baseChangedTraceHom {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
    (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    {ω : ModuleDerived X}
    [IsIso (baseChangeMate g' f' f g sq adj_f adj_f' ω)]
    (τ : (moduleDerivedPushforward f).obj ω ⟶ derivedStructureSheaf Y)
    {M' : ModuleDerived X'} (φ' : M' ⟶ (ModuleDerived.pullback g').obj ω) :
    (moduleDerivedPushforward f').obj M' ⟶ derivedStructureSheaf Y' :=
  (moduleDerivedPushforward f').map φ' ≫
    baseChangedTrace g' f' f g sq adj_f adj_f' τ

/-- The Hom-form comparison is `Rf'_*` followed by the base-changed trace. -/
theorem baseChangedTraceHom_eq {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
    (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    {ω : ModuleDerived X}
    [IsIso (baseChangeMate g' f' f g sq adj_f adj_f' ω)]
    (τ : (moduleDerivedPushforward f).obj ω ⟶ derivedStructureSheaf Y)
    {M' : ModuleDerived X'} (φ' : M' ⟶ (ModuleDerived.pullback g').obj ω) :
    baseChangedTraceHom g' f' f g sq adj_f adj_f' τ φ' =
      (moduleDerivedPushforward f').map φ' ≫
        baseChangedTrace g' f' f g sq adj_f adj_f' τ :=
  sorry

/-- After cartesian base change to an affine algebraic space, the pulled-back pair
`(L(g')^* ω, Lg^* τ)` is isomorphic to the twisted-inverse pair `(a'(𝒪_{Y'}), Tr)`.

The comparison uses the single canonical mate `β` of the cartesian square. The mate is
required to be an isomorphism, and `L(g)^* τ = β ≫ Rf'_*(e) ≫ Tr`. With `IsIso β` this
is equivalent to `inv β ≫ L(g)^* τ = Rf'_*(e) ≫ Tr` as maps `Rf'_* L(g')^* ω ⟶ 𝒪_{Y'}`. -/
def affineBaseChangeCondition {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (ω : ModuleDerived X)
    (τ : (moduleDerivedPushforward f).obj ω ⟶ derivedStructureSheaf Y) : Prop :=
  ∀ {X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [IsAffine Y'] [QuasiCompact f'] [QuasiSeparated f']
    (sq : IsPullback g' f' f g) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (adj : pushforwardCohomologyIn f' ⊣ a')
    (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
    (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)],
    IsIso (baseChangeMate g' f' f g sq adj_f adj_f' ω) ∧
      ∃ e : (ModuleDerived.pullback g').obj ω ≅ twistedInverseComplex f' a',
        pulledTrace f g τ =
          baseChangeMate g' f' f g sq adj_f adj_f' ω ≫
            (moduleDerivedPushforward f').map e.hom ≫ twistedInverseTrace f' a' adj

/-- Affine base change of a trace pair is invertibility of the cartesian mate together
with an isomorphism of complexes commuting with `Lg^* τ` and `Tr`. -/
theorem affineBaseChangeCondition_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (ω : ModuleDerived X)
    (τ : (moduleDerivedPushforward f).obj ω ⟶ derivedStructureSheaf Y) :
    affineBaseChangeCondition f ω τ ↔
      ∀ {X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
        [IsAffine Y'] [QuasiCompact f'] [QuasiSeparated f']
        (sq : IsPullback g' f' f g) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
        (adj : pushforwardCohomologyIn f' ⊣ a')
        (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
        (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
        [IsIso (ModuleDerived.pullbackCompComparison f' g)]
        [IsIso (ModuleDerived.pullbackCompComparison g' f)],
        IsIso (baseChangeMate g' f' f g sq adj_f adj_f' ω) ∧
          ∃ e : (ModuleDerived.pullback g').obj ω ≅ twistedInverseComplex f' a',
            pulledTrace f g τ =
              baseChangeMate g' f' f g sq adj_f adj_f' ω ≫
                (moduleDerivedPushforward f').map e.hom ≫
                  twistedInverseTrace f' a' adj :=
  sorry

/-- A relative dualizing complex for a proper, flat, finitely presented morphism of
algebraic spaces is a `Y`-perfect object of `D(𝒪_X)` equipped with a trace
`Rf_* ω ⟶ 𝒪_Y` whose cartesian base change to every affine algebraic space recovers
the twisted-inverse pair. -/
structure RelativeDualizingComplex {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f] where
  /-- The `Y`-perfect object `ω` of `D(𝒪_X)`. -/
  complex : ModuleDerived X
  /-- The trace `τ : Rf_* ω ⟶ 𝒪_Y`. -/
  trace : (moduleDerivedPushforward f).obj complex ⟶ derivedStructureSheaf Y
  /-- The complex is `Y`-perfect. -/
  isPerfect : IsPerfectRelativeTo f complex
  /-- After cartesian base change to an affine algebraic space, the pulled-back pair is
  isomorphic to the twisted-inverse pair. -/
  affineBaseChange : affineBaseChangeCondition f complex trace

namespace RelativeDualizingComplex

/-- Construct a relative dualizing complex from a `Y`-perfect complex, a trace, and the
affine base-change comparison. -/
noncomputable def of {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] (ω : ModuleDerived X)
    (τ : (moduleDerivedPushforward f).obj ω ⟶ derivedStructureSheaf Y)
    (hPerfect : IsPerfectRelativeTo f ω)
    (hAffine : affineBaseChangeCondition f ω τ) :
    RelativeDualizingComplex f where
  complex := ω
  trace := τ
  isPerfect := hPerfect
  affineBaseChange := hAffine

/-- On an affine target, the twisted-inverse pair `(a(𝒪_Y), Tr)` is a relative dualizing
complex. -/
noncomputable def ofTwistedInverse {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] [IsAffine Y]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a) :
    RelativeDualizingComplex f where
  complex := twistedInverseComplex f a
  trace := twistedInverseTrace f a adj
  isPerfect := sorry
  affineBaseChange := sorry

/-- A relative dualizing complex is `Y`-perfect and satisfies affine cartesian base
change to the twisted-inverse pair. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Proper f] [Flat f] [FinitePresentation f]
    (C : RelativeDualizingComplex f) :
    IsPerfectRelativeTo f C.complex ∧ affineBaseChangeCondition f C.complex C.trace :=
  sorry

/-- Affine cartesian squares against `ofOver T` for an affine scheme `T` recover the
textbook base-change comparison. -/
theorem ofOver_affineBaseChange {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Proper f] [Flat f] [FinitePresentation f]
    (C : RelativeDualizingComplex f) {T : Over S} [AlgebraicGeometry.IsAffine T.left]
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ ofOver T) (g : ofOver T ⟶ Y)
    [QuasiCompact f'] [QuasiSeparated f'] (sq : IsPullback g' f' f g)
    (a' : DerivedQCoh (ofOver T) ⥤ DerivedQCoh X')
    (adj : pushforwardCohomologyIn f' ⊣ a')
    (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
    (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)] :
    IsIso (baseChangeMate g' f' f g sq adj_f adj_f' C.complex) ∧
      ∃ e : (ModuleDerived.pullback g').obj C.complex ≅ twistedInverseComplex f' a',
        pulledTrace f g C.trace =
          baseChangeMate g' f' f g sq adj_f adj_f' C.complex ≫
            (moduleDerivedPushforward f').map e.hom ≫ twistedInverseTrace f' a' adj :=
  sorry

/-- After cartesian base change to an affine algebraic space, postcomposition with
`Lg^* τ ∘ Rf'_* (-)` is a Hom-space isomorphism
`Hom(M', L(g')^* ω) ≃ Hom(Rf'_* M', 𝒪_{Y'})`. -/
theorem affineBaseChange_hom {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Proper f] [Flat f] [FinitePresentation f]
    (C : RelativeDualizingComplex f) {X' Y' : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [IsAffine Y'] [QuasiCompact f'] [QuasiSeparated f']
    (sq : IsPullback g' f' f g)
    (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
    (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    [IsIso (baseChangeMate g' f' f g sq adj_f adj_f' C.complex)]
    (M' : DerivedQCoh X') :
    Function.Bijective
      (fun φ' : (inclusion X').obj M' ⟶ (ModuleDerived.pullback g').obj C.complex ↦
        baseChangedTraceHom g' f' f g sq adj_f adj_f' C.trace φ') :=
  sorry

end RelativeDualizingComplex

end AlgebraicGeometry.AlgebraicSpace

