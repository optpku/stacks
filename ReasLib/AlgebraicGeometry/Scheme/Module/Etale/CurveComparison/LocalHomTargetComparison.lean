/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommLocalHomComplex

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace LocalHomTargetComparison
variable {A R : Type (u + 1)} [CommRing A] [Ring R]
variable (h : A →+* R) (hc : ∀ (a : A) (r : R), h a * r = r * h a)
variable (Y : Scheme.{u})
variable [Y.smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable (L : ChainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ)
variable {J K : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℕ}
variable (g : J ⟶ K)

/-- Postcompose each actual finite-diagonal local Hom with the specified
target-complex component. This reuses Kuhn's objects, maps and differential. -/
def degreeMap (n : ℕ) : NoncommLocalHomComplex.degree h hc Y L J n ⟶
    NoncommLocalHomComplex.degree h hc Y L K n :=
  NoncommLocalHomComplex.lift h hc Y L K n (fun i ↦
    NoncommLocalHomComplex.projection h hc Y L J n i ≫
      NoncommLocalHom.postcomp h hc Y (g.f (n - i.val)))

def map : NoncommLocalHomComplex.complex h hc Y L J ⟶
    NoncommLocalHomComplex.complex h hc Y L K where
  f := degreeMap h hc Y L g
  comm' := by sorry

def integerMap : NoncommLocalHomComplex.integerComplex h hc Y L J ⟶
    NoncommLocalHomComplex.integerComplex h hc Y L K :=
  HomologicalComplex.extendMap (map h hc Y L g) ComplexShape.embeddingUpNat

/-- Target postcomposition for the curve-degree source uses the actual even shift. -/
def shiftedMap : NoncommLocalHomComplex.shiftedComplex h hc Y L J ⟶
    NoncommLocalHomComplex.shiftedComplex h hc Y L K :=
  (shiftFunctor (CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ)) ℤ) (2 : ℤ)).map
    (integerMap h hc Y L g)

end LocalHomTargetComparison
