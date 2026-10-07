module

public import ReasLib.AlgebraicGeometry.DividedPowers.Scheme
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Quasicoherent
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers

/-!
# Divided-power relative differentials

The divided-power quotient of relative differentials and its affine section API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open KaehlerDifferential.DeRham
open scoped AlgebraicGeometry RelativeDerivation

universe u

noncomputable section

/-- A sheaf derivation is divided-power compatible when it satisfies the divided-power relation
on every affine section of the divided-power scheme. -/
def DividedPowerScheme.RelativeDifferentials.IsDividedPower
    (T : DividedPowerScheme.{u}) (S : Scheme.{u}) (f : T.scheme ⟶ S)
    {M : T.scheme.Modules} (D : RingedSpace.Hom.derivations f.toShHom M) : Prop :=
  ∀ (W : T.scheme.affineOpens) (n : ℕ+) {x : Γ(T.scheme, W.1)},
    x ∈ T.ideal.ideal W →
      D.d ((T.dividedPowers W).dpow (n : ℕ) x) =
        (T.dividedPowers W).dpow ((n : ℕ) - 1) x • D.d x

/-- Divided-power compatibility is characterized by its affine-section relation. -/
theorem DividedPowerScheme.RelativeDifferentials.isDividedPower_iff
    (T : DividedPowerScheme.{u}) (S : Scheme.{u}) (f : T.scheme ⟶ S)
    {M : T.scheme.Modules} (D : RingedSpace.Hom.derivations f.toShHom M) :
    DividedPowerScheme.RelativeDifferentials.IsDividedPower T S f D ↔
      ∀ (W : T.scheme.affineOpens) (n : ℕ+) {x : Γ(T.scheme, W.1)},
        x ∈ T.ideal.ideal W →
          D.d ((T.dividedPowers W).dpow (n : ℕ) x) =
            (T.dividedPowers W).dpow ((n : ℕ) - 1) x • D.d x := sorry

/-- A divided-power-compatible relative derivation with values in a module sheaf on the source. -/
structure DividedPowerScheme.RelativeDifferentials.Derivation
    (T : DividedPowerScheme.{u}) (S : Scheme.{u}) (f : T.scheme ⟶ S)
    (M : T.scheme.Modules) where
  /-- The underlying relative derivation. -/
  toDerivation : RingedSpace.Hom.derivations f.toShHom M
  /-- The divided-power relation on affine sections. -/
  isDividedPower : DividedPowerScheme.RelativeDifferentials.IsDividedPower T S f toDerivation

/-- Construct a bundled divided-power-compatible relative derivation from its underlying
derivation and compatibility proof. -/
def DividedPowerScheme.RelativeDifferentials.Derivation.of
    (T : DividedPowerScheme.{u}) (S : Scheme.{u}) (f : T.scheme ⟶ S)
    (M : T.scheme.Modules)
    (toDerivation : RingedSpace.Hom.derivations f.toShHom M)
    (isDividedPower :
      DividedPowerScheme.RelativeDifferentials.IsDividedPower T S f toDerivation) :
    DividedPowerScheme.RelativeDifferentials.Derivation T S f M :=
  { toDerivation, isDividedPower }

/-- The module sheaf and quotient map representing divided-power relative differentials. -/
structure DividedPowerScheme.RelativeDifferentials
    (T : DividedPowerScheme.{u}) (S : Scheme.{u}) (f : T.scheme ⟶ S) where
  /-- The module sheaf of divided-power relative differentials. -/
  module : T.scheme.Modules
  /-- The quotient morphism from the ordinary relative differential sheaf. -/
  quotient : Ω[f.toShHom] ⟶ module
  /-- The quotient map induces a divided-power-compatible relative derivation. -/
  quotient_isDividedPower :
    DividedPowerScheme.RelativeDifferentials.IsDividedPower T S f
      ((d[f.toShHom]).postcomp quotient.val)
  /-- The quotient satisfies the universal factorization property for divided-power derivations. -/
  universal :
    ∀ (M : T.scheme.Modules)
      (D : DividedPowerScheme.RelativeDifferentials.Derivation T S f M),
      ∃! q : module ⟶ M,
        (d[f.toShHom]).postcomp (quotient ≫ q).val = D.toDerivation

/-- Construct a divided-power relative differential module from its quotient data. -/
def DividedPowerScheme.RelativeDifferentials.of
    (T : DividedPowerScheme.{u}) (S : Scheme.{u}) (f : T.scheme ⟶ S)
    (module : T.scheme.Modules) (quotient : Ω[f.toShHom] ⟶ module)
    (quotient_isDividedPower :
      DividedPowerScheme.RelativeDifferentials.IsDividedPower T S f
        ((d[f.toShHom]).postcomp quotient.val))
    (universal :
      ∀ (M : T.scheme.Modules)
        (D : DividedPowerScheme.RelativeDifferentials.Derivation T S f M),
        ∃! q : module ⟶ M,
          (d[f.toShHom]).postcomp (quotient ≫ q).val = D.toDerivation) :
    DividedPowerScheme.RelativeDifferentials T S f :=
  { module, quotient, quotient_isDividedPower, universal }

/-- The quotient relation and universal factorization property are the defining conditions of a
divided-power relative differential module. -/
theorem DividedPowerScheme.RelativeDifferentials.spec
    (D : DividedPowerScheme.RelativeDifferentials T S f) :
    DividedPowerScheme.RelativeDifferentials.IsDividedPower T S f
        ((d[f.toShHom]).postcomp D.quotient.val) ∧
      (∀ (M : T.scheme.Modules)
        (d : DividedPowerScheme.RelativeDifferentials.Derivation T S f M),
        ∃! q : D.module ⟶ M,
          (d[f.toShHom]).postcomp (D.quotient ≫ q).val = d.toDerivation) := sorry

/-- The component of the divided-power differential quotient on an open of the source. -/
def DividedPowerScheme.RelativeDifferentials.quotientApp
    {T : DividedPowerScheme.{u}} {S : Scheme.{u}} {f : T.scheme ⟶ S}
    (D : DividedPowerScheme.RelativeDifferentials T S f)
    (U : Opens T.scheme) :
    Γ(Ω[f.toShHom], U) → Γ(D.module, U) :=
  PresheafOfModules.Hom.app D.quotient.val (op U)

/-- The quotient map on sections is the sheaf morphism component. -/
theorem DividedPowerScheme.RelativeDifferentials.quotientApp_apply
    {T : DividedPowerScheme.{u}} {S : Scheme.{u}} {f : T.scheme ⟶ S}
    (D : DividedPowerScheme.RelativeDifferentials T S f)
    (U : Opens T.scheme) (x : Γ(Ω[f.toShHom], U)) :
    quotientApp D U x = PresheafOfModules.Hom.app D.quotient.val (op U) x :=
  sorry

/-- The divided-power differential quotient is a quasi-coherent module sheaf. -/
theorem DividedPowerScheme.RelativeDifferentials.module_isQuasicoherent
    (T : DividedPowerScheme.{u}) (S : Scheme.{u}) (f : T.scheme ⟶ S)
    (D : DividedPowerScheme.RelativeDifferentials T S f) :
    D.module.IsQuasicoherent := sorry

/-- On compatible affine opens, sections of the divided-power differential quotient are uniquely
linearly equivalent to the ring-level divided-power differential module, compatibly with the
universal divided-power derivation. -/
theorem DividedPowerScheme.RelativeDifferentials.existsUnique_affineSectionsLinearEquiv
    (T : DividedPowerScheme.{u}) (S : Scheme.{u}) (f : T.scheme ⟶ S)
    (D : DividedPowerScheme.RelativeDifferentials T S f)
    (W : T.scheme.affineOpens) (V : S.affineOpens)
    (hWV : W.1 ≤ f ⁻¹ᵁ V.1) :
    ∃! eΩ : Γ(D.module, W.1) ≃ₗ[Γ(T.scheme, W.1)]
      dividedPowerDifferential
        (f.appLE V.1 W.1 hWV).hom (T.dividedPowers W),
      ∀ a : Γ(T.scheme, W.1),
        eΩ (quotientApp D W.1 (((d[f.toShHom]).app (op W.1)).d a)) =
          dividedPowerDifferentialDerivation
            (f.appLE V.1 W.1 hWV).hom (T.dividedPowers W) a := sorry

end

end
