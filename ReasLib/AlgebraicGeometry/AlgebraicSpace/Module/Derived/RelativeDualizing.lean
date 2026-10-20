module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.StructureSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange.CellModel
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Single
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RestrictedPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Pullback

/-! # Relative dualizing complexes for proper flat morphisms of algebraic spaces -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The twisted inverse image `a(𝒪_Y)` of the derived structure sheaf, as an object of
`D(𝒪_X)`. -/
noncomputable def twistedInverseComplex {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) :
    ModuleDerived X :=
  (inclusion X).obj
    (a.obj ⟨structureSheafDerived Y, structureSheafDerived_mem Y⟩)

/-- The twisted inverse image is the included value of `a` on the derived structure sheaf. -/
theorem twistedInverseComplex_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) :
    twistedInverseComplex f a =
      (inclusion X).obj
        (a.obj ⟨structureSheafDerived Y, structureSheafDerived_mem Y⟩) := sorry

/-- The trace `Tr_{f, 𝒪_Y}` is the included counit of `Rf_* ⊣ a` at the derived structure
sheaf. -/
noncomputable def twistedInverseTrace {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a) :
    (moduleDerivedPushforward f).obj (twistedInverseComplex f a) ⟶
      structureSheafDerived Y :=
  let OY : DerivedQCoh Y := ⟨structureSheafDerived Y, structureSheafDerived_mem Y⟩
  (pushforwardCohomologyIn.inclusionIso f).inv.app (a.obj OY) ≫
    (inclusion Y).map (adj.counit.app OY)

/-- The twisted-inverse trace is the included counit of the chosen `D_QCoh` adjunction. -/
theorem twistedInverseTrace_counit {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a) :
    twistedInverseTrace f a adj =
      (pushforwardCohomologyIn.inclusionIso f).inv.app
          (a.obj ⟨structureSheafDerived Y, structureSheafDerived_mem Y⟩) ≫
        (inclusion Y).map
          (adj.counit.app ⟨structureSheafDerived Y, structureSheafDerived_mem Y⟩) := sorry

/-- The canonical comparison `L(g)^* 𝒪_Y ⟶ 𝒪_{Y'}` from derived pullback of the structure
sheaf to the structure sheaf of the source. -/
noncomputable def derivedStructureSheafPullback {S : Scheme.{u}} {Y' Y : AlgebraicSpace S}
    (g : Y' ⟶ Y) :
    (ModuleDerived.pullback g).obj (structureSheafDerived Y) ⟶ structureSheafDerived Y' :=
  ModuleDerived.singlePullbackComparison g
      (SheafOfModules.unit (structureSheaf Y) : Y.Modules) (0 : ℤ) ≫
    (DerivedCategory.singleFunctor (Modules Y') (0 : ℤ)).map (IdealSubobject.pullbackUnit g)

/-- Derived pullback of the structure sheaf compares with the structure sheaf of the source
through the single-object derived comparison and the underived unit comparison. -/
theorem derivedStructureSheafPullback_eq {S : Scheme.{u}} {Y' Y : AlgebraicSpace S}
    (g : Y' ⟶ Y) :
    derivedStructureSheafPullback g =
      ModuleDerived.singlePullbackComparison g
          (SheafOfModules.unit (structureSheaf Y) : Y.Modules) (0 : ℤ) ≫
        (DerivedCategory.singleFunctor (Modules Y') (0 : ℤ)).map
          (IdealSubobject.pullbackUnit g) := sorry

/-- The pulled-back trace `L(g)^* τ : L(g)^* Rf_* ω ⟶ 𝒪_{Y'}`. -/
noncomputable def pulledTrace {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y)
    (g : Y' ⟶ Y) {ω : ModuleDerived X}
    (τ : (moduleDerivedPushforward f).obj ω ⟶ structureSheafDerived Y) :
    (ModuleDerived.pullback g).obj ((moduleDerivedPushforward f).obj ω) ⟶
      structureSheafDerived Y' :=
  (ModuleDerived.pullback g).map τ ≫ derivedStructureSheafPullback g

/-- The pulled-back trace is derived pullback of `τ` followed by the structure-sheaf
comparison. -/
theorem pulledTrace_eq {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y)
    (g : Y' ⟶ Y) {ω : ModuleDerived X}
    (τ : (moduleDerivedPushforward f).obj ω ⟶ structureSheafDerived Y) :
    pulledTrace f g τ =
      (ModuleDerived.pullback g).map τ ≫ derivedStructureSheafPullback g := sorry

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
    (τ : (moduleDerivedPushforward f).obj ω ⟶ structureSheafDerived Y) :
    (moduleDerivedPushforward f').obj ((ModuleDerived.pullback g').obj ω) ⟶
      structureSheafDerived Y' :=
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
    (τ : (moduleDerivedPushforward f).obj ω ⟶ structureSheafDerived Y) :
    baseChangedTrace g' f' f g sq adj_f adj_f' τ =
      inv (baseChangeMate g' f' f g sq adj_f adj_f' ω) ≫ pulledTrace f g τ := sorry

/-- After cartesian base change to an affine algebraic space, the pulled-back pair
`(L(g')^* ω, Lg^* τ)` is isomorphic to the twisted-inverse pair `(a'(𝒪_{Y'}), Tr)`.

The comparison uses the single canonical mate `β` of the cartesian square. The mate is
required to be an isomorphism, and `L(g)^* τ = β ≫ Rf'_*(e) ≫ Tr`. With `IsIso β` this
is equivalent to `inv β ≫ L(g)^* τ = Rf'_*(e) ≫ Tr` as maps `Rf'_* L(g')^* ω ⟶ 𝒪_{Y'}`. -/
def affineBaseChangeCondition {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (ω : ModuleDerived X)
    (τ : (moduleDerivedPushforward f).obj ω ⟶ structureSheafDerived Y) : Prop :=
  ∀ {X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [IsAffine Y'] [QuasiCompact f'] [QuasiSeparated f']
    (sq : IsPullback g' f' f g) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (adj : pushforwardCohomologyIn f' ⊣ a'),
    IsIso (ModuleDerived.baseChangeMap g' f' f g sq ω) ∧
      ∃ e : (ModuleDerived.pullback g').obj ω ≅ twistedInverseComplex f' a',
        pulledTrace f g τ =
          ModuleDerived.baseChangeMap g' f' f g sq ω ≫
            (moduleDerivedPushforward f').map e.hom ≫ twistedInverseTrace f' a' adj

/-- Affine base change of a trace pair is invertibility of the cartesian mate together
with an isomorphism of complexes commuting with `Lg^* τ` and `Tr`. -/
theorem affineBaseChangeCondition_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (ω : ModuleDerived X)
    (τ : (moduleDerivedPushforward f).obj ω ⟶ structureSheafDerived Y) :
    affineBaseChangeCondition f ω τ ↔
      ∀ {X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
        [IsAffine Y'] [QuasiCompact f'] [QuasiSeparated f']
        (sq : IsPullback g' f' f g) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
        (adj : pushforwardCohomologyIn f' ⊣ a'),
        IsIso (ModuleDerived.baseChangeMap g' f' f g sq ω) ∧
          ∃ e : (ModuleDerived.pullback g').obj ω ≅ twistedInverseComplex f' a',
            pulledTrace f g τ =
              ModuleDerived.baseChangeMap g' f' f g sq ω ≫
                (moduleDerivedPushforward f').map e.hom ≫
                  twistedInverseTrace f' a' adj := sorry

/-- A relative dualizing complex for a proper, flat, finitely presented morphism of
algebraic spaces is a `Y`-perfect object of `D(𝒪_X)` equipped with a trace
`Rf_* ω ⟶ 𝒪_Y` whose cartesian base change to every affine algebraic space recovers
the twisted-inverse pair. -/
structure RelativeDualizingComplex {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] where
  /-- The `Y`-perfect object `ω` of `D(𝒪_X)`. -/
  complex : ModuleDerived X
  /-- The trace `τ : Rf_* ω ⟶ 𝒪_Y`. -/
  trace : (moduleDerivedPushforward f).obj complex ⟶ structureSheafDerived Y
  /-- The complex is `Y`-perfect. -/
  isPerfect : IsPerfectRelativeTo f complex
  /-- After cartesian base change to an affine algebraic space, the pulled-back pair is
  isomorphic to the twisted-inverse pair. -/
  affineBaseChange : affineBaseChangeCondition f complex trace

namespace RelativeDualizingComplex

/-- Construct a relative dualizing complex from a `Y`-perfect complex, a trace, and the
affine base-change comparison. -/
noncomputable def of {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    (ω : ModuleDerived X)
    (τ : (moduleDerivedPushforward f).obj ω ⟶ structureSheafDerived Y)
    (hPerfect : IsPerfectRelativeTo f ω)
    (hAffine : affineBaseChangeCondition f ω τ) :
    RelativeDualizingComplex f where
  complex := ω
  trace := τ
  isPerfect := hPerfect
  affineBaseChange := hAffine

/-- The twisted inverse image of the structure sheaf is relatively perfect for a
proper, flat, finitely presented morphism with affine target. -/
theorem twistedInverse_isPerfect {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] [IsAffine Y]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a) :
    IsPerfectRelativeTo f (twistedInverseComplex f a) := sorry

/-- The twisted-inverse pair satisfies the canonical affine base-change condition for a
proper, flat, finitely presented morphism with affine target. -/
theorem twistedInverse_affineBaseChange {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f] [IsAffine Y]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a) :
    affineBaseChangeCondition f (twistedInverseComplex f a) (twistedInverseTrace f a adj) := sorry

/-- On an affine target, the twisted-inverse pair is a relative dualizing complex. -/
noncomputable def ofTwistedInverse {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] [IsAffine Y]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a) :
    RelativeDualizingComplex f :=
  of f (twistedInverseComplex f a) (twistedInverseTrace f a adj)
    (twistedInverse_isPerfect f a adj) (twistedInverse_affineBaseChange f a adj)

/-- A relative dualizing complex is `Y`-perfect and satisfies affine cartesian base
change to the twisted-inverse pair. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Proper f] [Flat f] [FinitePresentation f]

    (C : RelativeDualizingComplex f) :
    IsPerfectRelativeTo f C.complex ∧ affineBaseChangeCondition f C.complex C.trace := sorry

/-- Affine cartesian squares against `ofOver T` for an affine scheme `T` recover the
canonical trace-compatible comparison with the twisted-inverse pair. -/
theorem ofOver_affineBaseChange {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Proper f] [Flat f] [FinitePresentation f]

    (C : RelativeDualizingComplex f) {T : Over S} [AlgebraicGeometry.IsAffine T.left]
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ ofOver T) (g : ofOver T ⟶ Y)
    [QuasiCompact f'] [QuasiSeparated f'] (sq : IsPullback g' f' f g)
    (a' : DerivedQCoh (ofOver T) ⥤ DerivedQCoh X')
    (adj : pushforwardCohomologyIn f' ⊣ a') :
    IsIso (ModuleDerived.baseChangeMap g' f' f g sq C.complex) ∧
      ∃ e : (ModuleDerived.pullback g').obj C.complex ≅ twistedInverseComplex f' a',
        pulledTrace f g C.trace =
          ModuleDerived.baseChangeMap g' f' f g sq C.complex ≫
            (moduleDerivedPushforward f').map e.hom ≫ twistedInverseTrace f' a' adj := sorry

/-- Two relative dualizing complexes for the same proper, flat, finitely presented
morphism of algebraic spaces admit a unique isomorphism of underlying complexes in
`D(𝒪_X)` making the traces commute. -/
theorem existsUniqueIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Proper f] [Flat f] [FinitePresentation f]
    (C D : RelativeDualizingComplex f) :
    ∃! e : C.complex ≅ D.complex,
      C.trace = (moduleDerivedPushforward f).map e.hom ≫ D.trace := sorry

end RelativeDualizingComplex

end AlgebraicGeometry.AlgebraicSpace
