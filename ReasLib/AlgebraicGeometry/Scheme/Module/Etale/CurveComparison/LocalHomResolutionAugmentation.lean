/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommLocalHomComplex
public import Mathlib.Algebra.Homology.Single

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace LocalHomResolutionAugmentation
variable {A R : Type (u + 1)} [CommRing A] [Ring R]
variable (h : A →+* R) (hc : ∀ (a : A) (r : R), h a * r = r * h a)
variable (Y : Scheme.{u})
variable [Y.smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)}
variable {K : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
variable (L : ChainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ)
variable (J : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℕ)
variable (α : L ⟶ (ChainComplex.single₀ _).obj F)
variable (β : (CochainComplex.single₀ _).obj K ⟶ J)

/-- Precompose with the ACTUAL degree-zero source augmentation and postcompose
with the ACTUAL target augmentation. The finite zero diagonal has one coordinate. -/
def zero : NoncommLocalHom.obj h hc Y F K ⟶
    (NoncommLocalHomComplex.complex h hc Y L J).X 0 :=
  NoncommLocalHomComplex.lift h hc Y L J 0 (fun i ↦ by
    have hi : i = (0 : Fin 1) := by
      apply Fin.ext
      have := i.isLt
      omega
    subst i
    exact NoncommLocalHom.map h hc Y (α.f 0) (β.f 0))

/-- The augmentation components land in cycles by both input chain-map laws. -/
theorem zero_d : zero h hc Y L J α β ≫
    (NoncommLocalHomComplex.complex h hc Y L J).d 0 1 = 0 := by sorry

/-- The concrete augmentation into Kuhn's existing Hom complex. No new local
Hom object, evaluation implementation, or resolution comparison is selected. -/
def map : (CochainComplex.single₀ _).obj (NoncommLocalHom.obj h hc Y F K) ⟶
    NoncommLocalHomComplex.complex h hc Y L J :=
  (CochainComplex.fromSingle₀Equiv _ _).symm ⟨zero h hc Y L J α β, zero_d h hc Y L J α β⟩

end LocalHomResolutionAugmentation
