/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.RegularImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.LocalizedChern
open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

noncomputable section

universe u

/- Lemma 42.55.3 (1): the positive localized Chern classes below the codimension vanish. -/
@[stacks 0FEG] #check (AlgebraicGeometry.LocalizedChern.chernClass_pushforwardStructureSheaf_eq_zero :
    ∀ {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [LocallyOfFiniteType (i ≫ p)] [hclosed : IsClosedImmersion i]
    [IsRegularImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (classes : ChernClass.Theory delta p)
    (hX : CompactSpace X ∨
      ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (t : ℕ) (ht : 0 < t) (htr : t < r),
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
      BivariantClass.pointwiseZero delta (overHom (i ≫ p) p i rfl) (t : ℤ))

/- Lemma 42.55.3 (2): the top localized Chern class is the signed factorial multiple of the normal-sheaf class. -/
@[stacks 0FEG] #check (AlgebraicGeometry.LocalizedChern.chernClass_pushforwardStructureSheaf_eq_normalClass :
    ∀ {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [LocallyOfFiniteType (i ≫ p)] [hclosed : IsClosedImmersion i]
    [IsRegularImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (classes : ChernClass.Theory delta p)
    (hX : CompactSpace X ∨
      ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (hr : 0 < r)
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i)
    (D : ClosedDeformation (i ≫ p) p i rfl (ofNormalSheaf i r e)),
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
        (((-1 : ℤ) ^ (r - 1)) * (Nat.factorial (r - 1) : ℤ)))

