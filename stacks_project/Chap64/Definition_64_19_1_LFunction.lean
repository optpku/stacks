module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap59.Definition_59_77_1
public import stacks_project.Chap59.Lemma_59_71_5
public import stacks_project.Chap64.Definition_64_19_1_EulerFactor
public import stacks_project.Chap64.Definition_64_19_1_FrobeniusStalk

/-!
# L-functions of constructible étale sheaves over finite fields

This leaf owns the geometric Euler product
`L(X, F) = ∏_{x ∈ |X|} det(1 - π_x^* T^{deg x} | F_x̄)⁻¹` in `Λ⟦T⟧`,
realised coefficientwise by finite products over closed points of bounded
residue degree, together with its extension to `D_ctf(X, Λ)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.SchemeOverField
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {Λ : Type u} [CommRing Λ] [Finite Λ] [IsNoetherianRing Λ]
variable [HasColimitsOfSize.{u, u} (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y : Scheme.{u}},
    MonoidalCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- There are only finitely many closed points of residue degree at most `n`
on a finite-type scheme over a finite field. -/
instance finite_closedPoints_residueDegreeLE (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom] (n : ℕ) :
    Finite {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n} := sorry

/-- A `Fintype` structure on the finite set of closed points of residue degree
at most `n`. -/
instance fintype_closedPoints_residueDegreeLE (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom] (n : ℕ) :
    Fintype {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n} :=
  Fintype.ofFinite _

/-- The source degree `[κ(x) : k]` is the residue degree of the structure
morphism at `x`. -/
theorem deg_eq_residueDegree (X : SchemeOverField k) (x : X.left) :
    X.hom.residueDegree x = Module.finrank k (X.left.residueField x) := sorry

/-- The local Euler factor of a constructible flat étale sheaf at a closed
point. -/
def eulerFactorClosedStalk (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hcons : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F] (x : closedPoints X.left) : PowerSeries Λ :=
  -- Local instance justification (proof-local temporary data): finite generation of a constructible-flat stalk is a consequence of the explicit constructible hypothesis, which is not a typeclass.
  haveI : Module.Finite Λ (geometricStalkClosed F x) :=
    finite_geometricStalkClosed F hcons x
  -- Local instance justification (proof-local temporary data): projectivity of a constructible-flat stalk is a consequence of `IsFlat` together with the explicit constructible hypothesis, which cannot register a global instance.
  haveI : Module.Projective Λ (geometricStalkClosed F x) :=
    projective_geometricStalkClosed F hcons x
  LinearMap.eulerFactor (geometricFrobeniusClosedStalk F x) (X.hom.residueDegree x.1)

/-- The constant coefficient of a closed-point Euler factor is `1`. -/
theorem constantCoeff_eulerFactorClosedStalk (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hcons : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F] (x : closedPoints X.left) :
    PowerSeries.constantCoeff (eulerFactorClosedStalk X F hcons x) = 1 := sorry

/-- The L-function of a constructible flat étale sheaf of `Λ`-modules on a
finite-type scheme over a finite field, as the Euler product over closed
points of the local factors `det(1 - π_x^* T^{deg x} | F_x̄)⁻¹`. -/
def lFunction (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hcons : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F] : PowerSeries Λ :=
  PowerSeries.mk fun n =>
    PowerSeries.coeff n
      (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n},
        eulerFactorClosedStalk X F hcons x.1)

/-- The coefficient of `T^n` in `lFunction` is the corresponding coefficient of
the finite product of Euler factors over closed points of residue degree at
most `n`. -/
theorem lFunction_coeff (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hcons : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F] (n : ℕ) :
    PowerSeries.coeff n (lFunction X hΛ F hcons) =
      PowerSeries.coeff n
        (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n},
          eulerFactorClosedStalk X F hcons x.1) := sorry

/-- The L-function is the Euler product over closed points of the local
factors `det(1 - π_x^* T^{deg x} | F_x̄)⁻¹`, realised coefficientwise by
finite products over residue degree at most `n`. -/
theorem lFunction_spec (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hcons : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F] :
    lFunction X hΛ F hcons =
      PowerSeries.mk fun n =>
        PowerSeries.coeff n
          (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n},
            eulerFactorClosedStalk X F hcons x.1) := sorry

/-- The local Euler factor of an object of `D_ctf(X, Λ)` at a closed point,
using an explicit perfectness hypothesis on the geometric stalk. That
hypothesis is the stalkwise content of finite Tor dimension, until a
canonical étale `locallyFiniteTorDimension` owner exists. -/
def eulerFactorDerivedStalk (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom]
    {locallyFiniteTorDimension : ObjectProperty (EtaleDerived X.left Λ)}
    (K : Scheme.EtaleConstructibleTorFinite X.left Λ
      (fun F ↦ Sheaf.IsConstructibleEtaleModule
        (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
        (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
      locallyFiniteTorDimension)
    (x : closedPoints X.left)
    (hperf : DerivedCategory.IsPerfect (geometricDerivedStalkClosed K.obj.obj x)) :
    PowerSeries Λ :=
  hperf.eulerFactor
    (geometricFrobeniusDerivedStalkClosed K.obj.obj x) (X.hom.residueDegree x.1)

/-- Unfolding of the derived closed-point Euler factor. -/
theorem eulerFactorDerivedStalk_def (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom]
    {locallyFiniteTorDimension : ObjectProperty (EtaleDerived X.left Λ)}
    (K : Scheme.EtaleConstructibleTorFinite X.left Λ
      (fun F ↦ Sheaf.IsConstructibleEtaleModule
        (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
        (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
      locallyFiniteTorDimension)
    (x : closedPoints X.left)
    (hperf : DerivedCategory.IsPerfect (geometricDerivedStalkClosed K.obj.obj x)) :
    eulerFactorDerivedStalk X K x hperf =
      hperf.eulerFactor
        (geometricFrobeniusDerivedStalkClosed K.obj.obj x)
        (X.hom.residueDegree x.1) := sorry

/-- The L-function of an object of `D_ctf(X, Λ)`, as the Euler product over
closed points of the local factors `det(1 - π_x^* T^{deg x} | K_x̄)⁻¹`.
The extra `hperf` hypothesis records that geometric stalks are perfect,
which is the stalkwise content of finite Tor dimension. -/
def lFunctionDerived (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    {locallyFiniteTorDimension : ObjectProperty (EtaleDerived X.left Λ)}
    (K : Scheme.EtaleConstructibleTorFinite X.left Λ
      (fun F ↦ Sheaf.IsConstructibleEtaleModule
        (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
        (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
      locallyFiniteTorDimension)
    (hperf : ∀ x : closedPoints X.left,
      DerivedCategory.IsPerfect (geometricDerivedStalkClosed K.obj.obj x)) :
    PowerSeries Λ :=
  PowerSeries.mk fun n ↦
    PowerSeries.coeff n
      (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n},
        eulerFactorDerivedStalk X K x.1 (hperf x.1))

/-- The coefficient of `T^n` in `lFunctionDerived` is the corresponding
coefficient of the finite product of derived Euler factors over closed points
of residue degree at most `n`. -/
theorem lFunctionDerived_coeff (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom] (hΛ : Nat.Coprime (Nat.card Λ) p)
    {locallyFiniteTorDimension : ObjectProperty (EtaleDerived X.left Λ)}
    (K : Scheme.EtaleConstructibleTorFinite X.left Λ
      (fun F ↦ Sheaf.IsConstructibleEtaleModule
        (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
        (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
      locallyFiniteTorDimension)
    (hperf : ∀ x : closedPoints X.left,
      DerivedCategory.IsPerfect (geometricDerivedStalkClosed K.obj.obj x))
    (n : ℕ) :
    PowerSeries.coeff n (lFunctionDerived X hΛ K hperf) =
      PowerSeries.coeff n
        (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n},
          eulerFactorDerivedStalk X K x.1 (hperf x.1)) := sorry

/-- On a constructible flat sheaf placed in degree zero, the sheaf-theoretic
L-function agrees with the derived L-function. -/
theorem lFunctionDerived_single (X : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom] (hΛ : Nat.Coprime (Nat.card Λ) p)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hcons : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F]
    {locallyFiniteTorDimension : ObjectProperty (EtaleDerived X.left Λ)}
    (K : Scheme.EtaleConstructibleTorFinite X.left Λ
      (fun G ↦ Sheaf.IsConstructibleEtaleModule
        (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
        (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) G)
      locallyFiniteTorDimension)
    (hperf : ∀ x : closedPoints X.left,
      DerivedCategory.IsPerfect (geometricDerivedStalkClosed K.obj.obj x))
    (hK : K.obj.obj =
      (DerivedCategory.singleFunctor
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj F) :
    lFunction X hΛ F hcons = lFunctionDerived X hΛ K hperf := sorry

end AlgebraicGeometry.SchemeOverField
