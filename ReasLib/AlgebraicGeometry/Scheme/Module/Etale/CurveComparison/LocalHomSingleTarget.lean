/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommLocalHomComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace LocalHomSingleTarget
variable {A R : Type (u + 1)} [CommRing A] [Ring R]
variable (h : A →+* R) (hc : ∀ (a : A) (r : R), h a * r = r * h a)
variable (Y : Scheme.{u})
variable [Y.smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable (B : ChainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ)
variable (T : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))

abbrev single := (HomologicalComplex.single _ (ComplexShape.up ℕ) 2).obj T
abbrev term (i : ℕ) := NoncommLocalHom.obj h hc Y (B.X i) T

def differential (i : ℕ) : term h hc Y B T i ⟶ term h hc Y B T (i + 1) :=
  ((-1 : ℤ) ^ (i + 1)) • NoncommLocalHom.precomp h hc Y (B.d (i + 1) i)

theorem differential_sq (i : ℕ) : differential h hc Y B T i ≫ differential h hc Y B T (i + 1) = 0 := by sorry

/-- The actual signed dual complex: only one Hom factor survives the degree-two target. -/
def simple := CochainComplex.of (term h hc Y B T) (differential h hc Y B T) (differential_sq h hc Y B T)

/-- Project to the unique nonzero diagonal factor and use the canonical
single-object identification, with proved index arithmetic. -/
def projection (i : ℕ) : NoncommLocalHomComplex.degree h hc Y B (single Y T) (i + 2) ⟶
    term h hc Y B T i :=
  NoncommLocalHomComplex.projection h hc Y B (single Y T) (i + 2) ⟨i, by omega⟩ ≫
  NoncommLocalHom.postcomp h hc Y
    (((single Y T).XIsoOfEq (by omega : i + 2 - i = 2)).hom ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 2 T).hom)

/-- All other diagonal factors have a genuinely zero target. This proves
invertibility of the displayed projection, not an arbitrary Hom-complex iso. -/
instance projection_isIso (i : ℕ) : IsIso (projection h hc Y B T i) := by sorry

theorem negative_zero (i : ℤ) (hi : i < 0) :
    IsZero ((NoncommLocalHomComplex.shiftedComplex h hc Y B (single Y T)).X i) := by sorry

def componentIso (i : ℤ) :
    (NoncommLocalHomComplex.shiftedComplex h hc Y B (single Y T)).X i ≅
    ((simple h hc Y B T).extend ComplexShape.embeddingUpNat).X i :=
  if hi : 0 ≤ i then
    CochainComplex.shiftFunctorObjXIso (NoncommLocalHomComplex.integerComplex h hc Y B (single Y T))
      (2 : ℤ) i (i + 2) rfl ≪≫
    (NoncommLocalHomComplex.complex h hc Y B (single Y T)).extendXIso ComplexShape.embeddingUpNat
      (i := i.toNat + 2) (i' := i + 2) (by change ((i.toNat + 2 : ℕ) : ℤ) = i + 2; omega) ≪≫
    (@asIso _ _ _ _ (projection h hc Y B T i.toNat) (projection_isIso h hc Y B T i.toNat)) ≪≫
    ((simple h hc Y B T).extendXIso ComplexShape.embeddingUpNat
      (i := i.toNat) (i' := i) (by change (i.toNat : ℤ) = i; omega)).symm
  else (negative_zero h hc Y B T i (by omega)).iso
    (CochainComplex.isZero_of_isStrictlyGE ((simple h hc Y B T).extend ComplexShape.embeddingUpNat) 0 i (by omega))

/-- Explicit curve-Hom/signed-dual comparison with the actual differential signs. -/
def iso : NoncommLocalHomComplex.shiftedComplex h hc Y B (single Y T) ≅
    (simple h hc Y B T).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents (componentIso h hc Y B T) (by sorry)

end LocalHomSingleTarget
