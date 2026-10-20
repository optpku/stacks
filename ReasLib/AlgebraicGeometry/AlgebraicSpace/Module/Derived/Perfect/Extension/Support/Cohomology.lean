/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Extension.Support

/-!
# Finite-shift decompositions and cohomology control for supported perfect extensions

A supported perfect complex on a quasi-compact open subspace admits a compatible
perfect extension whose restriction is a finite biproduct of positive shifts and the
original complex. A supported retract extension can also be chosen to induce
cohomology-sheaf isomorphisms above any prescribed degree.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- On a quasi-compact, quasi-separated algebraic space, a map from a supported
perfect derived module on a quasi-compact open subspace extends from a globally
supported perfect module whose restriction is the biproduct of the original module
and finitely many positive shifts with finite multiplicities. The inclusion of the
original summand is compatible with the given map. -/
theorem exists_supported_finiteShift_extension {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (W : OpenSubspace X)
    [IsQuasiCompact W.X] (T : Closeds (Points X))
    (hT : QuasiCompact (OpenSubspace.fromOpens T.compl).ι) (E : DerivedQCoh X)
    (P : ModuleDerived W.X) (hP : ModuleDerived.IsPerfect P)
    (hP_support :
      ModuleDerived.IsSupportedOn P (Points.map W.ι ⁻¹' (T : Set (Points X))))
    (α : P ⟶ (ModuleDerived.pullback W.ι).obj E.obj) :
    ∃ (R : ModuleDerived X) (hR : ModuleDerived.IsPerfect R)
      (hR_support : ModuleDerived.IsSupportedOn R (T : Set (Points X)))
      (β : R ⟶ E.obj) (m : ℕ) (n : Fin m → ℕ)
      (e : (P ⊞ (⨁ fun (j : Fin m) => ⨁ fun (_ : Fin (n j)) =>
        P⟦((j.val : ℤ) + 1)⟧)) ≅ (ModuleDerived.pullback W.ι).obj R),
      (Limits.biprod.inl ≫ e.hom) ≫ (ModuleDerived.pullback W.ι).map β = α :=
  sorry

/-- A supported perfect extension of a map from a perfect derived module on a
quasi-compact open subspace can be chosen so that the retract inclusion induces
cohomology-sheaf isomorphisms in every degree strictly above a prescribed cutoff. -/
theorem exists_supported_retract_extension_isIso_above {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (W : OpenSubspace X) [IsQuasiCompact W.X] (T : Closeds (Points X))
    (hT : QuasiCompact (OpenSubspace.fromOpens T.compl).ι) (E : DerivedQCoh X)
    (P : ModuleDerived W.X) (hP : ModuleDerived.IsPerfect P)
    (hP_support :
      ModuleDerived.IsSupportedOn P (Points.map W.ι ⁻¹' (T : Set (Points X))))
    (α : P ⟶ (ModuleDerived.pullback W.ι).obj E.obj) (a : ℤ) :
    ∃ (R : ModuleDerived X) (hR : ModuleDerived.IsPerfect R)
      (hR_support : ModuleDerived.IsSupportedOn R (T : Set (Points X)))
      (β : R ⟶ E.obj) (r : Retract P ((ModuleDerived.pullback W.ι).obj R)),
      r.i ≫ (ModuleDerived.pullback W.ι).map β = α ∧
        ∀ i : ℤ, a < i →
          IsIso ((DerivedCategory.homologyFunctor (Modules W.X) i).map r.i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
