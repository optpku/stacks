module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Frobenius.Derived
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Trace
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
import Mathlib.Tactic.CrossRefAttribute

/-! # Global Lefschetz numbers -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open Opposite ComplexShape
open scoped AlgebraicGeometry

universe u

noncomputable section

open scoped Ring

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {Λ : Type u} [Ring Λ] [Finite Λ]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    ∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable (X : SchemeOverField k)
variable [Curve X] [Projective X.hom]

/-- The global Lefschetz number is the commutator-quotient trace of geometric
Frobenius acting on perfect geometric derived global sections. -/
@[stacks 03TX]
def globalLefschetzNumber
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    (hK : DerivedCategory.IsPerfect (geometricRGamma X K)) :
    Λ♮ :=
  hK.traceNatural (geometricFrobeniusRGamma X K)

/-- The global Lefschetz number is the finite-projective trace of `π_X^*` on
`RΓ(X_k̄, K|_{X_k̄})`. -/
theorem globalLefschetzNumber_spec
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    (hK : DerivedCategory.IsPerfect (geometricRGamma X K)) :
    globalLefschetzNumber X K hK =
      hK.traceNatural (geometricFrobeniusRGamma X K) :=
  rfl

end AlgebraicGeometry.SchemeOverField
