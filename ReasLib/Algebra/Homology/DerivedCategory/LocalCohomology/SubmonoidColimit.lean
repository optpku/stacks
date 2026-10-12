/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import ReasLib.Algebra.Group.Submonoid.Divisibility
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.SupportRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealComplement

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace CategoryTheory.DerivedCategory.LocalCohomology

variable {A : Type u} [CommRing A]

/-- Divisibility of elements reverses inclusion of their principal ideals. -/
theorem spanSingleton_antitone {S : Submonoid A} {f g : S.Divisibility}
    (hfg : f ≤ g) : Ideal.span {(g : A)} ≤ Ideal.span {(f : A)} := sorry

/-- The degree-`i` local-cohomology object supported on the zero locus of a
member of `S`. -/
noncomputable abbrev divisibilityStage (S : Submonoid A) (M : ModuleCat A)
    (RΓ : (f : S.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (Ideal.span {(f : A)}))
    (i : ℤ) (f : S.Divisibility) : ModuleCat A :=
  supportedCohomology (Ideal.span {(f : A)}) (RΓ f) M i

/-- The local-cohomology transition map associated to divisibility in `S`. -/
noncomputable def divisibilityTransition (S : Submonoid A) (M : ModuleCat A)
    (RΓ : (f : S.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (Ideal.span {(f : A)}))
    (hRΓ : ∀ f : S.Divisibility,
      IdealPowerTorsion.inclusion (Ideal.span {(f : A)}) ⊣ RΓ f)
    (i : ℤ) {f g : S.Divisibility} (e : f ⟶ g) :
    divisibilityStage S M RΓ i f ⟶ divisibilityStage S M RΓ i g :=
  (DerivedCategory.homologyFunctor (ModuleCat A) i).map
    (supportRestrictionAmbientApp (spanSingleton_antitone (leOfHom e))
      (RΓ g) (RΓ f) (hRΓ g) (hRΓ f) (ModuleCat.single0 M))

/-- The local-cohomology transition attached to an identity is an identity. -/
theorem divisibilityTransition_id (S : Submonoid A) (M : ModuleCat A)
    (RΓ : (f : S.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (Ideal.span {(f : A)}))
    (hRΓ : ∀ f : S.Divisibility,
      IdealPowerTorsion.inclusion (Ideal.span {(f : A)}) ⊣ RΓ f)
    (i : ℤ) (f : S.Divisibility) :
    divisibilityTransition S M RΓ hRΓ i (𝟙 f) = 𝟙 _ := sorry

/-- Local-cohomology transition maps respect composition. -/
theorem divisibilityTransition_comp (S : Submonoid A) (M : ModuleCat A)
    (RΓ : (f : S.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (Ideal.span {(f : A)}))
    (hRΓ : ∀ f : S.Divisibility,
      IdealPowerTorsion.inclusion (Ideal.span {(f : A)}) ⊣ RΓ f)
    (i : ℤ) {f g h : S.Divisibility} (e : f ⟶ g) (e' : g ⟶ h) :
    divisibilityTransition S M RΓ hRΓ i (e ≫ e') =
      divisibilityTransition S M RΓ hRΓ i e ≫
        divisibilityTransition S M RΓ hRΓ i e' := sorry

/-- The filtered diagram `f ↦ H^i_{V(f)}(M)` indexed by divisibility in `S`. -/
noncomputable def divisibilityDiagram (S : Submonoid A) (M : ModuleCat A)
    (RΓ : (f : S.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (Ideal.span {(f : A)}))
    (hRΓ : ∀ f : S.Divisibility,
      IdealPowerTorsion.inclusion (Ideal.span {(f : A)}) ⊣ RΓ f)
    (i : ℤ) : S.Divisibility ⥤ ModuleCat A where
  obj f := divisibilityStage S M RΓ i f
  map e := divisibilityTransition S M RΓ hRΓ i e
  map_id f := divisibilityTransition_id S M RΓ hRΓ i f
  map_comp e e' := divisibilityTransition_comp S M RΓ hRΓ i e e'

/-- The degree-zero supported-cohomology stage maps canonically to `M`. -/
noncomputable def zeroStageMap (S : Submonoid A) (M : ModuleCat A)
    (RΓ : (f : S.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (Ideal.span {(f : A)}))
    (hRΓ : ∀ f : S.Divisibility,
      IdealPowerTorsion.inclusion (Ideal.span {(f : A)}) ⊣ RΓ f)
    (f : S.Divisibility) :
    (divisibilityDiagram S M RΓ hRΓ 0).obj f ⟶ M :=
  (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
      ((hRΓ f).counit.app (ModuleCat.single0 M)) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) 0).hom.app M

/-- The degree-zero stage maps are compatible with divisibility transitions. -/
theorem zeroStageMap_naturality (S : Submonoid A) (M : ModuleCat A)
    (RΓ : (f : S.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (Ideal.span {(f : A)}))
    (hRΓ : ∀ f : S.Divisibility,
      IdealPowerTorsion.inclusion (Ideal.span {(f : A)}) ⊣ RΓ f)
    {f g : S.Divisibility} (e : f ⟶ g) :
    (divisibilityDiagram S M RΓ hRΓ 0).map e ≫ zeroStageMap S M RΓ hRΓ g =
      zeroStageMap S M RΓ hRΓ f ≫ 𝟙 M := sorry

/-- The canonical degree-zero cocone over local cohomology with supports `V(f)`. -/
noncomputable def zeroCocone (S : Submonoid A) (M : ModuleCat A)
    (RΓ : (f : S.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (Ideal.span {(f : A)}))
    (hRΓ : ∀ f : S.Divisibility,
      IdealPowerTorsion.inclusion (Ideal.span {(f : A)}) ⊣ RΓ f) :
    Cocone (divisibilityDiagram S M RΓ hRΓ 0) :=
  Cocone.mk M
    { app := zeroStageMap S M RΓ hRΓ
      naturality := fun {_ _} e ↦ zeroStageMap_naturality S M RΓ hRΓ e }

/-- The canonical map from the colimit of the modules `H^0_{V(f)}(M)` to `M`. -/
noncomputable def zeroComparison (S : Submonoid A) (M : ModuleCat A)
    (RΓ : (f : S.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (Ideal.span {(f : A)}))
    (hRΓ : ∀ f : S.Divisibility,
      IdealPowerTorsion.inclusion (Ideal.span {(f : A)}) ⊣ RΓ f) :
    colimit (divisibilityDiagram S M RΓ hRΓ 0) ⟶ M :=
  colimit.desc (divisibilityDiagram S M RΓ hRΓ 0) (zeroCocone S M RΓ hRΓ)

/-- If localizing `M` at `S` gives zero, the canonical map from the colimit of
the modules `H^0_{V(f)}(M)` to `M` is an isomorphism. -/
theorem zeroComparisonIsIso (S : Submonoid A) (M : ModuleCat A)
    [Subsingleton (LocalizedModule S M)]
    (RΓ : (f : S.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (Ideal.span {(f : A)}))
    (hRΓ : ∀ f : S.Divisibility,
      IdealPowerTorsion.inclusion (Ideal.span {(f : A)}) ⊣ RΓ f) :
    IsIso (zeroComparison S M RΓ hRΓ) := sorry

/-- If localizing `M` at `S` gives zero, the filtered colimit of the modules
`H^1_{V(f)}(M)` for `f ∈ S` is zero. -/
theorem colimitDegreeOneIsZero (S : Submonoid A) (M : ModuleCat A)
    [Subsingleton (LocalizedModule S M)]
    (RΓ : (f : S.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (Ideal.span {(f : A)}))
    (hRΓ : ∀ f : S.Divisibility,
      IdealPowerTorsion.inclusion (Ideal.span {(f : A)}) ⊣ RΓ f) :
    IsZero (colimit (divisibilityDiagram S M RΓ hRΓ 1)) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology
