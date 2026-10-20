/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Classes
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.NormalSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.StructureSheaf.PerfectClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Perfect

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open Scheme.Hom.VirtualNormalBundle

/-- The pushed-forward structure sheaf of a regular closed immersion satisfies the
rank-bounded localized-Chern hypotheses in every positive degree. -/
theorem pushforwardStructureSheafSituation
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [LocallyOfFiniteType (i ≫ p)] [hclosed : IsClosedImmersion i]
    [IsRegularImmersion i]
    (hX : CompactSpace X ∨
      ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (t : ℕ) (ht : 0 < t) :
    @Situation (S := S) (δ := delta) (X := Over.mk p) (Z := Z) (i := i)
      _ _ _ hclosed
      (Scheme.DerivedQCoh.pushforwardStructureSheaf i).obj t .rankBound := sorry

/-- The positive localized Chern classes of `i_* 𝒪_Z` below the
codimension of a regular closed immersion vanish. -/
theorem chernClass_pushforwardStructureSheaf_eq_zero
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [LocallyOfFiniteType (i ≫ p)] [hclosed : IsClosedImmersion i]
    [IsRegularImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (classes : ChernClass.Theory delta p)
    (hX : CompactSpace X ∨
      ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (t : ℕ) (ht : 0 < t) (htr : t < r) :
    let E := (Scheme.DerivedQCoh.pushforwardStructureSheaf i).obj
    let setup := pushforwardStructureSheafSituation delta p i hX t ht
    @chernClass (S := S) (δ := delta) (X := Over.mk p) (Z := Z) (i := i)
        _ _ _ hclosed classes E
        (@Situation.perfect (S := S) (δ := delta) (X := Over.mk p)
          (Z := Z) (i := i) (E := E) (p := t) (mode := .rankBound) _ _ _ hclosed setup) t
        (@Situation.offCenter (S := S) (δ := delta) (X := Over.mk p)
          (Z := Z) (i := i) (E := E) (p := t) (mode := .rankBound) _ _ _ hclosed setup)
        (@Situation.finiteness (S := S) (δ := delta) (X := Over.mk p)
          (Z := Z) (i := i) (E := E) (p := t) (mode := .rankBound) _ _ _ hclosed setup) =
      BivariantClass.pointwiseZero delta (overHom (i ≫ p) p i rfl) (t : ℤ) := sorry

/-- The degree-`r` localized Chern class of `i_* 𝒪_Z` is
`(-1)^(r - 1) * (r - 1)!` times the normal-sheaf bivariant class. -/
theorem chernClass_pushforwardStructureSheaf_eq_normalClass
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [LocallyOfFiniteType (i ≫ p)] [hclosed : IsClosedImmersion i]
    [IsRegularImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (classes : ChernClass.Theory delta p)
    (hX : CompactSpace X ∨
      ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (hr : 0 < r)
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i)
    (D : ClosedDeformation (i ≫ p) p i rfl (ofNormalSheaf i r e)) :
    let E := (Scheme.DerivedQCoh.pushforwardStructureSheaf i).obj
    let setup := pushforwardStructureSheafSituation delta p i hX r hr
    @chernClass (S := S) (δ := delta) (X := Over.mk p) (Z := Z) (i := i)
        _ _ _ hclosed classes E
        (@Situation.perfect (S := S) (δ := delta) (X := Over.mk p)
          (Z := Z) (i := i) (E := E) (p := r) (mode := .rankBound) _ _ _ hclosed setup) r
        (@Situation.offCenter (S := S) (δ := delta) (X := Over.mk p)
          (Z := Z) (i := i) (E := E) (p := r) (mode := .rankBound) _ _ _ hclosed setup)
        (@Situation.finiteness (S := S) (δ := delta) (X := Over.mk p)
          (Z := Z) (i := i) (E := E) (p := r) (mode := .rankBound) _ _ _ hclosed setup) =
      BivariantClass.pointwiseZsmul delta (overHom (i ≫ p) p i rfl) (r : ℤ)
        (normalClass delta p i r e D)
        (((-1 : ℤ) ^ (r - 1)) * (Nat.factorial (r - 1) : ℤ)) := sorry

end AlgebraicGeometry.LocalizedChern
