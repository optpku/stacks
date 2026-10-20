/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Finite.Defs
public import stacks_project.Chap87.Definition_87_11_1_Formal

/-!
# Finite étale affine atlases of formal algebraic spaces

A sheaf on `(Sch/S)_fppf` has a finite étale affine atlas when it admits a
Definition 87.11.1 covering by finitely many affine formal algebraic spaces,
and it has an affine étale cover when a single affine formal algebraic space
maps to it by a representable étale locally surjective morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- A sheaf on `(Sch/S)_fppf` admits a finite étale affine atlas when there is
a jointly surjective family of representable étale maps from affine formal
algebraic spaces indexed by a finite type, as in Definition 87.11.1. -/
def HasFiniteAffineEtaleAtlas {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  ∃ (ι : Type (max u v)) (_ : Finite ι)
    (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
      (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
        (∀ i, etale (π i)) ∧
          Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π)

namespace HasFiniteAffineEtaleAtlas

/-- A finite étale affine atlas unpacks as a finite-index cofan of affine
formal algebraic spaces with representable étale charts whose coproduct
descends to a locally surjective map. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    HasFiniteAffineEtaleAtlas X ↔
      ∃ (ι : Type (max u v)) (_ : Finite ι)
        (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
          (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
            (∀ i, etale (π i)) ∧
              Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) := sorry

/-- A finite étale affine atlas supplies a finite family `{X_ i ⟶ X}` of
representable étale maps from affine formal algebraic spaces whose coproduct
is locally surjective. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : HasFiniteAffineEtaleAtlas X) :
    ∃ (ι : Type (max u v)) (_ : Finite ι)
      (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
        (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
          (∀ i, representableByAlgebraicSpaces (π i)) ∧
            (∀ i, etale (π i)) ∧
              Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) := sorry

end HasFiniteAffineEtaleAtlas

/-- A sheaf on `(Sch/S)_fppf` admits an affine étale cover when there is a
representable étale locally surjective morphism from an affine formal
algebraic space. -/
def HasAffineEtaleCover {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  ∃ (Y : Sheaf (𝒮.bigTopology S) (Type (max u v))) (f : Y ⟶ X),
    IsAffineFormalAlgebraicSpace Y ∧ etale f ∧ Sheaf.IsLocallySurjective f

namespace HasAffineEtaleCover

/-- An affine étale cover unpacks as a representable étale locally surjective
morphism from an affine formal algebraic space. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    HasAffineEtaleCover X ↔
      ∃ (Y : Sheaf (𝒮.bigTopology S) (Type (max u v))) (f : Y ⟶ X),
        IsAffineFormalAlgebraicSpace Y ∧ etale f ∧
          Sheaf.IsLocallySurjective f := sorry

/-- An affine étale cover supplies a morphism `Y ⟶ X` which is representable
by algebraic spaces, étale, and locally surjective, with `Y` an affine formal
algebraic space. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : HasAffineEtaleCover X) :
    ∃ (Y : Sheaf (𝒮.bigTopology S) (Type (max u v))) (f : Y ⟶ X),
      IsAffineFormalAlgebraicSpace Y ∧ representableByAlgebraicSpaces f ∧
        etale f ∧ Sheaf.IsLocallySurjective f := sorry

/-- The identity of an affine formal algebraic space is an affine étale
cover. -/
theorem of_isAffineFormalAlgebraicSpace {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] : HasAffineEtaleCover X := sorry

end HasAffineEtaleCover

end AlgebraicGeometry.IsFormalAlgebraicSpace
