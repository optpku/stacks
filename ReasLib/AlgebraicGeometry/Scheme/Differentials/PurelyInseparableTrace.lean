/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module


public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Extension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Finite
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.FieldTheory.PurelyInseparable.HigherTrace
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.RingHom.PurelyInseparable

@[expose] public section

open CategoryTheory AlgebraicGeometry Polynomial
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PurelyInseparableTrace


/-- The pushforward of the relative exterior-power module on `Y` along a finite morphism. -/
abbrev sourceModule
    (p : ℕ) [Fact p.Prime] (S : SchemeOverField (ZMod p)) (X Y : Over S.left)
    (f : Y ⟶ X) (i : ℕ) : X.left.Modules :=
  (Scheme.Modules.pushforward f.left).obj
    ((Λ[i] Ω[Y.hom.toShHom]) : Y.left.Modules)

/-- The reflexive-hull target formed from a relative exterior-power module on `X`. -/
abbrev targetModule
    (p : ℕ) [Fact p.Prime] (S : SchemeOverField (ZMod p)) (X : Over S.left)
    (i : ℕ) : X.left.Modules :=
  Scheme.Modules.reflexiveHull ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules)

/-- The stalk comparisons used to identify a scheme-level generic trace with the field-level
trace. The coefficient ring is the stalk of `S` at the image of the generic point of `X`, while
the source and target coefficients are the actual function fields of `Y` and `X`; the two
additive equivalences are required to respect the canonical local-ring actions. -/
def isCompatibleGenericStalkComparison
    {p : ℕ} [Fact p.Prime]
    (S : SchemeOverField (ZMod p)) (X Y : Over S.left)
    [IsIntegral X.left] [IsIntegral Y.left]
    (f : Y ⟶ X) [IsDominant f.left]
    (i : ℕ)
    {Λ R K : Type u} [CommRing Λ] [CommRing R] [CommRing K]
    [Algebra (ZMod p) Λ] [Algebra (ZMod p) R] [Algebra Λ R]
    [IsScalarTower (ZMod p) Λ R] [Nontrivial R]
    [Algebra R K] [Algebra Λ K] [IsScalarTower Λ R K]
    (rEquiv : R ≃+* X.left.functionField)
    (kEquiv : K ≃+* Y.left.functionField)
    (h_map : algebraMap R K =
      kEquiv.symm.toRingHom.comp
        ((f.left.functionFieldMap f.left.map_genericPoint_eq_of_isDominant).comp
          rEquiv.toRingHom))
    (ρ : X.left.presheaf.stalk (genericPoint X.left) →+* R)
    (τ : RingedSpace.stalkModuleCat
      (sourceModule p S X Y f i) (genericPoint X.left) ⟶
      RingedSpace.stalkModuleCat
        ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules) (genericPoint X.left))
    (a : R) (e : K ≃ₐ[R] AdjoinRoot (Polynomial.X ^ p - Polynomial.C a))
    (sourceComparison :
        (RingedSpace.stalkModuleCat (sourceModule p S X Y f i)
        (genericPoint X.left)) ≃+
        RestrictScalars R K
          (KaehlerDifferential.DeRham.Form Λ K i))
    (targetComparison :
      (RingedSpace.stalkModuleCat
        ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules) (genericPoint X.left)) ≃+
        KaehlerDifferential.DeRham.Form Λ R i) : Prop :=
  (algebraMap R K =
      kEquiv.symm.toRingHom.comp
        ((f.left.functionFieldMap f.left.map_genericPoint_eq_of_isDominant).comp
          rEquiv.toRingHom)) ∧
  (∀ (r : X.left.presheaf.stalk (genericPoint X.left)) (m),
      sourceComparison (r • m) =
        ρ r •
          sourceComparison m) ∧
    (∀ (r : X.left.presheaf.stalk (genericPoint X.left)) (m),
      targetComparison (r • m) =
        ρ r •
          targetComparison m) ∧
    (∀ m, targetComparison (τ.hom m) =
      PurelyInseparableTrace.Higher.traceOfEquiv
        (Λ := Λ) (R := R) (S := K)
        p (Fact.out : p.Prime) a e i (sourceComparison m))

/-- The compatible comparison specification exposes the transported field-level trace equation. -/
theorem isCompatibleGenericStalkComparison_spec
    {p : ℕ} [Fact p.Prime]
    (S : SchemeOverField (ZMod p)) (X Y : Over S.left)
    [IsIntegral X.left] [IsIntegral Y.left]
    (f : Y ⟶ X) [IsDominant f.left] (i : ℕ)
    {Λ R K : Type u} [CommRing Λ] [CommRing R] [CommRing K]
    [Algebra (ZMod p) Λ] [Algebra (ZMod p) R] [Algebra Λ R]
    [IsScalarTower (ZMod p) Λ R] [Nontrivial R]
    [Algebra R K] [Algebra Λ K] [IsScalarTower Λ R K]
    (rEquiv : R ≃+* X.left.functionField)
    (kEquiv : K ≃+* Y.left.functionField)
    (h_map : algebraMap R K =
      kEquiv.symm.toRingHom.comp
        ((f.left.functionFieldMap f.left.map_genericPoint_eq_of_isDominant).comp
          rEquiv.toRingHom))
    (ρ : X.left.presheaf.stalk (genericPoint X.left) →+* R)
    (τ : RingedSpace.stalkModuleCat
      (sourceModule p S X Y f i) (genericPoint X.left) ⟶
      RingedSpace.stalkModuleCat
        ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules) (genericPoint X.left))
    (a : R) (e : K ≃ₐ[R] AdjoinRoot (Polynomial.X ^ p - Polynomial.C a))
    (sourceComparison :
      (RingedSpace.stalkModuleCat (sourceModule p S X Y f i)
        (genericPoint X.left)) ≃+
        RestrictScalars R K (KaehlerDifferential.DeRham.Form Λ K i))
    (targetComparison :
      (RingedSpace.stalkModuleCat
        ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules) (genericPoint X.left)) ≃+
        KaehlerDifferential.DeRham.Form Λ R i)
    (h : isCompatibleGenericStalkComparison S X Y f i rEquiv kEquiv h_map ρ τ a e
      sourceComparison targetComparison) :
    ∀ m, targetComparison (τ.hom m) =
      PurelyInseparableTrace.Higher.traceOfEquiv
        (Λ := Λ) (R := R) (S := K)
        p (Fact.out : p.Prime) a e i (sourceComparison m) := sorry

/-- A specified comparison object transports field-level higher traces to generic stalks.
Its comparison map is accompanied by the scalar-action and pointwise trace specifications used by
the generic-stalk trace characterization. -/
structure GenericStalkComparison
    {p : ℕ} [Fact p.Prime]
    (S : SchemeOverField (ZMod p)) (X Y : Over S.left)
    [IsIntegral X.left] [IsIntegral Y.left]
    (f : Y ⟶ X) [IsFinite f.left] [IsDominant f.left]
    (i : ℕ)
    (L R K : Type u) [CommRing L] [CommRing R] [CommRing K]
    [Algebra (ZMod p) L] [Algebra (ZMod p) R] [Algebra L R]
    [IsScalarTower (ZMod p) L R] [Nontrivial R]
    [Algebra R K] [Algebra L K] [IsScalarTower L R K] where
  coefficientComparison : L ≃ₐ[ZMod p]
    S.left.presheaf.stalk (X.hom (genericPoint X.left))
  sourceFieldEquiv : R ≃+* X.left.functionField
  targetFieldEquiv : K ≃+* Y.left.functionField
  functionFieldMap_spec : algebraMap R K =
    targetFieldEquiv.symm.toRingHom.comp
      ((f.left.functionFieldMap f.left.map_genericPoint_eq_of_isDominant).comp
        sourceFieldEquiv.toRingHom)
  rho : X.left.presheaf.stalk (genericPoint X.left) →+* R
  rho_spec : ∀ r, sourceFieldEquiv (rho r) =
    algebraMap (X.left.presheaf.stalk (genericPoint X.left)) X.left.functionField r
  a : R
  e : K ≃ₐ[R] AdjoinRoot (Polynomial.X ^ p - Polynomial.C a)
  sourceComparison :
    (RingedSpace.stalkModuleCat (sourceModule p S X Y f i)
      (genericPoint X.left)) ≃+
      RestrictScalars R K (KaehlerDifferential.DeRham.Form L K i)
  targetComparison :
    (RingedSpace.stalkModuleCat
      ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules)
      (genericPoint X.left)) ≃+
      KaehlerDifferential.DeRham.Form L R i
  comparison :
    (RestrictScalars R K (KaehlerDifferential.DeRham.Form L K i) →ₗ[R]
      KaehlerDifferential.DeRham.Form L R i) →
      (RingedSpace.stalkModuleCat (sourceModule p S X Y f i)
        (genericPoint X.left) ⟶
        RingedSpace.stalkModuleCat
          ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules)
          (genericPoint X.left))
  sourceComparison_smul : ∀ (r : X.left.presheaf.stalk (genericPoint X.left)) (m),
    sourceComparison (r • m) = rho r • sourceComparison m
  targetComparison_smul : ∀ (r : X.left.presheaf.stalk (genericPoint X.left)) (m),
    targetComparison (r • m) = rho r • targetComparison m
  comparison_spec : ∀ (T : RestrictScalars R K
      (KaehlerDifferential.DeRham.Form L K i) →ₗ[R]
      KaehlerDifferential.DeRham.Form L R i) (m),
    targetComparison ((comparison T).hom m) = T (sourceComparison m)

/-- The specified comparison map attached to a generic-stalk comparison object. -/
noncomputable def GenericStalkComparison.map
    {p : ℕ} [Fact p.Prime]
    {S : SchemeOverField (ZMod p)} {X Y : Over S.left}
    [IsIntegral X.left] [IsIntegral Y.left]
    {f : Y ⟶ X} [IsFinite f.left] [IsDominant f.left]
    {i : ℕ} {L R K : Type u} [CommRing L] [CommRing R] [CommRing K]
    [Algebra (ZMod p) L] [Algebra (ZMod p) R] [Algebra L R]
    [IsScalarTower (ZMod p) L R] [Nontrivial R]
    [Algebra R K] [Algebra L K] [IsScalarTower L R K]
    (C : GenericStalkComparison S X Y f i L R K)
    (T : RestrictScalars R K (KaehlerDifferential.DeRham.Form L K i) →ₗ[R]
      KaehlerDifferential.DeRham.Form L R i) :
    RingedSpace.stalkModuleCat (sourceModule p S X Y f i) (genericPoint X.left) ⟶
      RingedSpace.stalkModuleCat ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules)
        (genericPoint X.left) :=
  C.comparison T

/-- A generic-point comparison for the field-level trace, with the extension algebra fixed by the
function-field map of the given morphism. -/
def isHigherTraceAtGenericPoint
    {p : ℕ} [Fact p.Prime]
    (S : SchemeOverField (ZMod p)) (X Y : Over S.left)
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    (f : Y ⟶ X) [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    (i : ℕ) (h_i : 1 ≤ i)
    (τ : RingedSpace.stalkModuleCat
      (sourceModule p S X Y f i) (genericPoint X.left) ⟶
      RingedSpace.stalkModuleCat
        ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules) (genericPoint X.left)) : Prop :=
  let Λ := S.left.presheaf.stalk (X.hom (genericPoint X.left))
  -- Local instance justification (proof-local temporary data): install the canonical base-field algebra on the stalk of `S` at the image of the generic point of `X` only while interpreting the comparison predicate.
  letI : Algebra (ZMod p) Λ :=
    inferInstance
  ∃ (hZR : Algebra (ZMod p) X.left.functionField)
    (hZK : Algebra (ZMod p) Y.left.functionField)
    (hΛR : Algebra Λ X.left.functionField)
    (hΛK : Algebra Λ Y.left.functionField)
    (hZΛR : IsScalarTower (ZMod p) Λ X.left.functionField)
    (hZΛK : IsScalarTower (ZMod p) Λ Y.left.functionField)
    (hRK : Algebra X.left.functionField Y.left.functionField)
    (hΛRK : IsScalarTower Λ X.left.functionField Y.left.functionField),
    -- Local instance justification (proof-local temporary data): install the existentially supplied base-field algebra on the function field of `X` only while interpreting the comparison predicate.
    letI : Algebra (ZMod p) X.left.functionField := hZR
    -- Local instance justification (proof-local temporary data): install the existentially supplied base-field algebra on the function field of `Y` only while interpreting the comparison predicate.
    letI : Algebra (ZMod p) Y.left.functionField := hZK
    -- Local instance justification (proof-local temporary data): install the existentially supplied base-stalk algebra on the function field of `X` only while interpreting the comparison predicate.
    letI : Algebra Λ X.left.functionField := hΛR
    -- Local instance justification (proof-local temporary data): install the existentially supplied base-stalk algebra on the function field of `Y` only while interpreting the comparison predicate.
    letI : Algebra Λ Y.left.functionField := hΛK
    -- Local instance justification (proof-local temporary data): install the existentially supplied base-field/base-stalk scalar tower on the function field of `X` only while interpreting the comparison predicate.
    letI : IsScalarTower (ZMod p) Λ X.left.functionField := hZΛR
    -- Local instance justification (proof-local temporary data): install the existentially supplied base-field/base-stalk scalar tower on the function field of `Y` only while interpreting the comparison predicate.
    letI : IsScalarTower (ZMod p) Λ Y.left.functionField := hZΛK
    -- Local instance justification (proof-local temporary data): install the existentially supplied function-field extension algebra only while interpreting the comparison predicate.
    letI : Algebra X.left.functionField Y.left.functionField := hRK
    -- Local instance justification (proof-local temporary data): install the existentially supplied base-stalk/function-field extension scalar tower only while interpreting the comparison predicate.
    letI : IsScalarTower Λ X.left.functionField Y.left.functionField := hΛRK
    ∃ (h_map : algebraMap X.left.functionField Y.left.functionField =
      f.left.functionFieldMap f.left.map_genericPoint_eq_of_isDominant),
      ∃ (a : X.left.functionField)
        (e : Y.left.functionField ≃ₐ[X.left.functionField]
          AdjoinRoot (Polynomial.X ^ p - Polynomial.C a)),
        ∃ (sourceComparison :
            (RingedSpace.stalkModuleCat (sourceModule p S X Y f i)
              (genericPoint X.left)) ≃+
                RestrictScalars X.left.functionField Y.left.functionField
                (KaehlerDifferential.DeRham.Form Λ Y.left.functionField i))
          (targetComparison :
            (RingedSpace.stalkModuleCat
              ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules)
              (genericPoint X.left)) ≃+
              KaehlerDifferential.DeRham.Form Λ X.left.functionField i),
          isCompatibleGenericStalkComparison (Λ := Λ) S X Y f i
            (RingEquiv.refl _) (RingEquiv.refl _) h_map
            (algebraMap (X.left.presheaf.stalk (genericPoint X.left))
              X.left.functionField)
            τ a e sourceComparison targetComparison

/-- The generic-stalk higher-trace characterization determines a stalk morphism uniquely. -/
theorem isHigherTraceAtGenericPoint_unique
    (p : ℕ) [Fact p.Prime]
    (S : SchemeOverField (ZMod p))
    (X Y : Over S.left)
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    (f : Y ⟶ X) [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    (i : ℕ) (h_i : 1 ≤ i)
    {τ₁ τ₂ : RingedSpace.stalkModuleCat (sourceModule p S X Y f i)
      (genericPoint X.left) ⟶
      RingedSpace.stalkModuleCat ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules)
        (genericPoint X.left)}
    (hτ₁ : isHigherTraceAtGenericPoint S X Y f hX hY h_pi h_degree i h_i τ₁)
    (hτ₂ : isHigherTraceAtGenericPoint S X Y f hX hY h_pi h_degree i h_i τ₂) :
    τ₁ = τ₂ := sorry

/-- A generic-stalk trace equipped with a presentation-independent higher-trace property. -/
structure CanonicalGenericTrace
    {p : ℕ} [Fact p.Prime]
    (S : SchemeOverField (ZMod p)) (X Y : Over S.left)
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    (f : Y ⟶ X) [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    (i : ℕ) (h_i : 1 ≤ i) where
  trace : RingedSpace.stalkModuleCat (sourceModule p S X Y f i) (genericPoint X.left) ⟶
    RingedSpace.stalkModuleCat ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules)
      (genericPoint X.left)
  isCanonical : isHigherTraceAtGenericPoint S X Y f hX hY h_pi h_degree i h_i trace

/-- Construction of a canonical generic-stalk trace from an auxiliary comparison object. -/
noncomputable def CanonicalGenericTrace.fromComparison
    {p : ℕ} [Fact p.Prime]
    (S : SchemeOverField (ZMod p)) (X Y : Over S.left)
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    (f : Y ⟶ X) [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    (i : ℕ) (h_i : 1 ≤ i)
    {L R K : Type u} [CommRing L] [CommRing R] [CommRing K]
    [Algebra (ZMod p) L] [Algebra (ZMod p) R] [Algebra L R]
    [IsScalarTower (ZMod p) L R] [Nontrivial R]
    [Algebra R K] [Algebra L K] [IsScalarTower L R K]
    (comparison : GenericStalkComparison S X Y f i L R K) :
    CanonicalGenericTrace S X Y f hX hY h_pi h_degree i h_i :=
  { trace := comparison.map
      (PurelyInseparableTrace.Higher.traceOfEquiv
        (Λ := L) (R := R) (S := K)
        p (Fact.out : p.Prime) comparison.a comparison.e i)
    isCanonical := sorry }

/-- The trace field of a canonical generic-stalk trace satisfies the higher-trace predicate. -/
theorem CanonicalGenericTrace.isHigherTrace
    {p : ℕ} [Fact p.Prime]
    {S : SchemeOverField (ZMod p)} {X Y : Over S.left}
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    {f : Y ⟶ X} [IsFinite f.left] [IsDominant f.left]
    {hX : X.left.isNormal} {hY : Y.left.isNormal}
    {h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable}
    {h_degree : f.left.inducedFunctionFieldDegree = p}
    {i : ℕ} {h_i : 1 ≤ i}
    (C : CanonicalGenericTrace S X Y f hX hY h_pi h_degree i h_i) :
    isHigherTraceAtGenericPoint S X Y f hX hY h_pi h_degree i h_i C.trace := sorry

/-- Canonical generic-stalk traces have the same underlying stalk morphism. -/
theorem canonicalGenericTrace_unique
    {p : ℕ} [Fact p.Prime]
    {S : SchemeOverField (ZMod p)} {X Y : Over S.left}
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    {f : Y ⟶ X} [IsFinite f.left] [IsDominant f.left]
    {hX : X.left.isNormal} {hY : Y.left.isNormal}
    {h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable}
    {h_degree : f.left.inducedFunctionFieldDegree = p}
    {i : ℕ} {h_i : 1 ≤ i}
    {C D : CanonicalGenericTrace S X Y f hX hY h_pi h_degree i h_i} :
    C.trace = D.trace := sorry

/-- The finite/noetherian hypotheses transport coherence from `Ω[X/S]` to the positive exterior
power modules used by the reflexive-hull extension. -/
theorem coherentExteriorPowers_of_source
    {p : ℕ} [Fact p.Prime]
    {S : SchemeOverField (ZMod p)} {X Y : Over S.left}
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    {f : Y ⟶ X} [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    {i : ℕ} (h_i : 1 ≤ i)
    [SheafOfModules.IsCoherent (Ω[X.hom.toShHom])] :
    SheafOfModules.IsCoherent (Λ[i] Ω[X.hom.toShHom]) ∧
      SheafOfModules.IsCoherent (Λ[i] Ω[Y.hom.toShHom]) := sorry

/-- The generic-stalk trace selected by its presentation-independent characterization. -/
noncomputable def genericTrace
    {p : ℕ} [Fact p.Prime]
    {S : SchemeOverField (ZMod p)} {X Y : Over S.left}
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    {f : Y ⟶ X} [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    {i : ℕ} (h_i : 1 ≤ i) :
    RingedSpace.stalkModuleCat (sourceModule p S X Y f i) (genericPoint X.left) ⟶
      RingedSpace.stalkModuleCat ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules)
        (genericPoint X.left) :=
  Classical.epsilon fun τ ↦
    isHigherTraceAtGenericPoint S X Y f hX hY h_pi h_degree i h_i τ

/-- The selected generic trace satisfies its presentation-independent characterization. -/
theorem genericTrace_spec
    {p : ℕ} [Fact p.Prime]
    {S : SchemeOverField (ZMod p)} {X Y : Over S.left}
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    {f : Y ⟶ X} [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    {i : ℕ} (h_i : 1 ≤ i) :
    isHigherTraceAtGenericPoint S X Y f hX hY h_pi h_degree i h_i
      (genericTrace hX hY h_pi h_degree h_i) := sorry

/-- The presentation-independent characterization uniquely determines the selected generic trace. -/
theorem genericTrace_unique
    {p : ℕ} [Fact p.Prime]
    {S : SchemeOverField (ZMod p)} {X Y : Over S.left}
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    {f : Y ⟶ X} [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    {i : ℕ} (h_i : 1 ≤ i)
    {τ : RingedSpace.stalkModuleCat (sourceModule p S X Y f i) (genericPoint X.left) ⟶
      RingedSpace.stalkModuleCat ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules)
        (genericPoint X.left)}
    (hτ : isHigherTraceAtGenericPoint S X Y f hX hY h_pi h_degree i h_i τ) :
    τ = genericTrace hX hY h_pi h_degree h_i := sorry

/-- The scheme-level morphism obtained by inverting the generic-stalk map on the prescribed
reflexive-hull extension. This construction does not consume a proof-level existence witness. -/
noncomputable def constructedTraceMap
    {p : ℕ} [Fact p.Prime]
    {S : SchemeOverField (ZMod p)} {X Y : Over S.left}
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    {f : Y ⟶ X} [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    {i : ℕ} (h_i : 1 ≤ i)
    [SheafOfModules.IsCoherent (Ω[X.hom.toShHom])] :
    sourceModule p S X Y f i ⟶ targetModule p S X i :=
  Function.invFun
    (fun φ : sourceModule p S X Y f i ⟶ targetModule p S X i ↦
      RingedSpace.moduleStalkHom (genericPoint X.left) φ)
    (genericTrace hX hY h_pi h_degree h_i ≫
      RingedSpace.moduleStalkHom (genericPoint X.left)
        (Scheme.Modules.toReflexiveHull
          ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules)))

/-- The constructed scheme-level trace has the prescribed generic-stalk extension property. -/
theorem constructedTraceMap_spec
    {p : ℕ} [Fact p.Prime]
    {S : SchemeOverField (ZMod p)} {X Y : Over S.left}
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    {f : Y ⟶ X} [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    {i : ℕ} (h_i : 1 ≤ i)
    [SheafOfModules.IsCoherent (Ω[X.hom.toShHom])] :
    RingedSpace.moduleStalkHom (genericPoint X.left)
        (constructedTraceMap hX hY h_pi h_degree h_i) =
      genericTrace hX hY h_pi h_degree h_i ≫
        RingedSpace.moduleStalkHom (genericPoint X.left)
          (Scheme.Modules.toReflexiveHull
            ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules)) := sorry

/-- The generic-stalk equation specifying the canonical extension to the reflexive hull. -/
def canonicalTraceMapSpec
    (p : ℕ) [Fact p.Prime]
    (S : SchemeOverField (ZMod p)) (X Y : Over S.left)
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    (f : Y ⟶ X) [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    (i : ℕ) (h_i : 1 ≤ i)
    [SheafOfModules.IsCoherent (Ω[X.hom.toShHom])]
    (φ : sourceModule p S X Y f i ⟶ targetModule p S X i) : Prop :=
  RingedSpace.moduleStalkHom (genericPoint X.left) φ =
    genericTrace hX hY h_pi h_degree h_i ≫
      RingedSpace.moduleStalkHom (genericPoint X.left)
        (Scheme.Modules.toReflexiveHull
          ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules))

/-- The canonical scheme-level trace morphism for a finite purely inseparable degree-`p` map. -/
noncomputable def traceMap
    (p : ℕ) [Fact p.Prime]
    (S : SchemeOverField (ZMod p))
    (X Y : Over S.left)
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    (f : Y ⟶ X) [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    (i : ℕ) (h_i : 1 ≤ i)
    [SheafOfModules.IsCoherent (Ω[X.hom.toShHom])] :
    sourceModule p S X Y f i ⟶ targetModule p S X i :=
  constructedTraceMap hX hY h_pi h_degree h_i

/-- The generic stalk of the canonical trace morphism satisfies its defining equation. -/
theorem traceMap_spec
    (p : ℕ) [Fact p.Prime]
    (S : SchemeOverField (ZMod p))
    (X Y : Over S.left)
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    (f : Y ⟶ X) [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    (i : ℕ) (h_i : 1 ≤ i)
    [SheafOfModules.IsCoherent (Ω[X.hom.toShHom])] :
    canonicalTraceMapSpec p S X Y f hX hY h_pi h_degree i h_i
      (traceMap p S X Y f hX hY h_pi h_degree i h_i) := sorry

/-- The generic-stalk equation uniquely determines the canonical scheme-level trace. -/
theorem traceMap_unique
    (p : ℕ) [Fact p.Prime]
    (S : SchemeOverField (ZMod p))
    (X Y : Over S.left)
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    (f : Y ⟶ X) [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    (i : ℕ) (h_i : 1 ≤ i)
    [SheafOfModules.IsCoherent (Ω[X.hom.toShHom])]
    {φ : sourceModule p S X Y f i ⟶ targetModule p S X i}
    (hφ : canonicalTraceMapSpec p S X Y f hX hY h_pi h_degree i h_i φ) :
    φ = traceMap p S X Y f hX hY h_pi h_degree i h_i := sorry

end AlgebraicGeometry.Scheme.PurelyInseparableTrace
