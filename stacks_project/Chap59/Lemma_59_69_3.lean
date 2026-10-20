/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.EtaleCohomology.AffineCurve
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.AssociatedModule
open SheafOfModules.RingedSite

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Curve X] [Smooth X.hom] [IsAffine X.left]
variable (n : ℕ)
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable (Xbar : SchemeOverField k) [Curve Xbar] [Smooth Xbar.hom] [Projective Xbar.hom]
variable (j : X.left ⟶ Xbar.left) [IsOpenImmersion j]
variable (h_over : j ≫ Xbar.hom = X.hom)
variable (g r : ℕ) (h_genus : AlgebraicGeometry.Curve.genus Xbar = g)
variable (h_r : Nat.card {x : Xbar.left | x ∉ j.opensRange} = r)
variable (h_finite : {x : Xbar.left | x ∉ j.opensRange}.Finite)
variable (h_pos : 0 < n) (h_n : IsUnit (n : k)) (q : ℕ) (hq : 2 ≤ q)

/- Lemma 59.69.3 (1) -/
@[stacks 03RR] #check (AlgebraicGeometry.EtaleCohomology.AffineCurve.rootsH0 X n h_pos h_n :
    ((Sheaf.functorH X.left.smallEtaleTopology 0).obj
        (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
          (smallCommStructureSheaf .etale X.left) n)) ≃+
      Additive (rootsOfUnity n k))

/- Lemma 59.69.3 (2) -/
@[stacks 03RR] #check (AlgebraicGeometry.EtaleCohomology.AffineCurve.rootsH1 X n
    Xbar j h_over g r h_genus h_r h_finite h_pos h_n :
    Nonempty
      (((Sheaf.functorH X.left.smallEtaleTopology 1).obj
        (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
          (smallCommStructureSheaf .etale X.left) n)) ≃+
        (Fin (2 * g + r - 1) → ZMod n)))

/- Lemma 59.69.3 (3) -/
@[stacks 03RR] #check (AlgebraicGeometry.EtaleCohomology.AffineCurve.roots_isZero X n
    h_pos h_n q hq :
    IsZero
      ((Sheaf.functorH X.left.smallEtaleTopology q).obj
        (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
          (smallCommStructureSheaf .etale X.left) n)))
