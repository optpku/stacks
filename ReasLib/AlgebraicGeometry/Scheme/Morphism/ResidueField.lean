/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.SetTheory.Cardinal.ENat

/-!
# Residue fields of scheme morphisms

This leaf provides the canonical algebra structure on the residue fields
induced by a morphism of schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A scheme morphism induces the canonical algebra structure
`κ(f(x)) → κ(x)` on residue fields. -/
noncomputable instance residueFieldAlgebra {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Algebra (S.residueField (f x)) (X.residueField x) :=
  (f.residueFieldMap x).hom.toAlgebra

/-- The transcendence degree of the residue field extension, including infinite degree. -/
noncomputable abbrev residueFieldTranscendenceDegreeAt {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) : ℕ∞ :=
  Cardinal.toENat (Algebra.trdeg (S.residueField (f x)) (X.residueField x))

/-- The natural-number projection of the residue-field transcendence degree.
This projection sends infinite degree to zero; finite-degree geometric interfaces
must establish finiteness before using it. -/
noncomputable abbrev residueFieldTrdegAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : ℕ :=
  Cardinal.toNat (Algebra.trdeg (S.residueField (f x)) (X.residueField x))

/-- The ring equivalence induced by a bijective residue-field map commutes
with the canonical algebra maps from the residue field of the image point. -/
theorem residueFieldAlgEquivOfBijective_commutes
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h : Function.Bijective (f.residueFieldMap x).hom)
    (r : S.residueField (f x)) :
    (RingEquiv.ofBijective (f.residueFieldMap x).hom h)
        ((algebraMap (S.residueField (f x)) (S.residueField (f x))) r) =
      (algebraMap (S.residueField (f x)) (X.residueField x)) r := sorry

/-- A bijective residue-field map induced by a scheme morphism is canonically
an algebra equivalence over the residue field of the image point. -/
noncomputable def residueFieldAlgEquivOfBijective
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h : Function.Bijective (f.residueFieldMap x).hom) :
    S.residueField (f x) ≃ₐ[S.residueField (f x)] X.residueField x :=
  let e : S.residueField (f x) ≃+* X.residueField x :=
    RingEquiv.ofBijective (f.residueFieldMap x).hom h
  @AlgEquiv.ofRingEquiv (S.residueField (f x)) (S.residueField (f x))
    (X.residueField x) _ _ _ _ _ e (residueFieldAlgEquivOfBijective_commutes f x h)

/-- Bijectivity of the residue-field maps `κ(g(f(x))) → κ(x)` and
`κ(f(x)) → κ(x)` implies bijectivity of `κ(g(f(x))) → κ(f(x))`. -/
theorem residueFieldMap_bijective_of_triangle {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
    (hκ : Function.Bijective (f.residueFieldMap x).hom)
    (hκs : Function.Bijective ((f ≫ g).residueFieldMap x).hom) :
    Function.Bijective (g.residueFieldMap (f x)).hom := sorry

namespace ResidueField

/-- A morphism `f : X ⟶ Spec k` induces the canonical `k`-algebra structure on the residue
field of every point of `X`. -/
@[stacks 0C52]
noncomputable abbrev algebraOfSpec
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    Algebra k (X.residueField x) :=
  (((f.residueFieldMap x).hom).comp
      (((Scheme.Spec.residueFieldIso (CommRingCat.of k) (f x)).inv).hom.comp
        (algebraMap k (f x).asIdeal.ResidueField))).toAlgebra

/-- The ring map underlying `algebraOfSpec`.  This is the canonical map
`k →+* κ(x)` attached to a point of a scheme over `Spec k`; downstream statements can use it
without introducing a local algebra instance merely to expose `algebraMap k κ(x)`. -/
noncomputable abbrev mapOfSpec
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    k →+* X.residueField x :=
  @algebraMap k (X.residueField x) _ _ (algebraOfSpec f x)

end ResidueField

end AlgebraicGeometry.Scheme.Hom
