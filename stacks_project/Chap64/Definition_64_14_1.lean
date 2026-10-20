module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Lefschetz.Global
import StacksCheckRecall

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

/- Definition 64.14.1. Let Λ be a finite ring, X a projective curve over a finite
field k, and K an object of D_ctf(X, Λ), for example the constant coefficient
complex. The canonical comparison c_K : π_X⁻¹ K ⟶ K, after base change to the
geometric fibre, induces π_X^* on RΓ(X_k̄, K|_{X_k̄}). The global Lefschetz number
is the trace of this action in Λ♮.
For K in D_ctf, geometric derived global sections are perfect. The definition
below extends to any complex with perfect geometric derived global sections;
this perfectness condition is not an identification with D_ctf. -/
@[stacks 03TX] #check
  (AlgebraicGeometry.SchemeOverField.globalLefschetzNumber :
    ∀ (X : SchemeOverField k)
      (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
      (hK : DerivedCategory.IsPerfect (geometricRGamma X K)), Λ♮)

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
  rfl

end AlgebraicGeometry.SchemeOverField
