/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import stacks_project.Chap64.Definition_64_14_1_Comparison
public import stacks_project.Chap64.Proposition_64_10_2_Trace
import Mathlib.Tactic.CrossRefAttribute

/-!
# Global Lefschetz number

The trace of geometric Frobenius on derived global sections of a constructible
complex of finite Tor-dimension on a projective curve over a finite field,
valued in the additive commutator quotient `Λ♮`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.SchemeOverField
open Opposite ComplexShape
open scoped AlgebraicGeometry Ring

universe u

noncomputable section

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

/-- Definition 64.14.1. Let `Λ` be a finite ring, `X` a projective curve over a
finite field `k`, and `K` an object of `D_ctf(X, Λ)` (for instance
`K = underline Λ`). There is a canonical map
`c_K : π_X⁻¹ K ⟶ K`, and its base change `c_K|_{X_k̄}` induces an action
denoted `π_X^*` on the perfect complex `RΓ(X_k̄, K|_{X_k̄})`. The global
Lefschetz number of `K` is the trace `Tr(π_X^* | RΓ(X_k̄, K))` of that
action. It is an element of `Λ♮`. Here `c_K` is
`geometricFrobeniusComparison`, the geometric restriction is
`geometricRestrictionDerived`, `RΓ` is `geometricRGamma`, and `π_X^*` is
`geometricFrobeniusRGamma`; the load-bearing elaborating hypothesis is
perfectness of `geometricRGamma X K`, recording that `K` lies in `D_ctf`. -/
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
  sorry

/-- The constant sheaf of coefficients, viewed as a derived object in degree
zero. This is the parenthetical example `K = underline Λ` of
Definition 64.14.1. -/
def constantCoefficient :
    DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  (DerivedCategory.singleFunctor
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj
    ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj (.of Λ Λ))

/-- The constant coefficient complex is the degree-zero embedding of
`underline Λ`. -/
theorem constantCoefficient_eq :
    constantCoefficient X =
      (DerivedCategory.singleFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj
        ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (.of Λ Λ)) :=
  sorry

end AlgebraicGeometry.SchemeOverField
