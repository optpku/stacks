/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.GroupScheme.IdentityComponent
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.FiniteProductColimit

/-!
# Affine opens in group schemes

This file establishes affine-open containment results for morphisms into group schemes.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.GroupScheme

/-- Let `G` be a Jacobson group scheme over an algebraically closed field `k`, with every closed
point rational over `k`. If the coordinate algebra of an affine `k`-scheme `T` is a directed
colimit of finite products of copies of `k`, then the range of every morphism `T ⟶ G` is
contained in an affine open of `G`. -/
theorem exists_affineOpen_containing_range_of_finitePiColimit
    {k I : Type u} [Field k] [IsAlgClosed k] [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (G : SchemeOverField k) [GrpObj G] [JacobsonSpace G.left]
    (h_rational : ∀ x : closedPoints G.left, IsIso (G.hom.residueFieldMap x.1))
    (F : I ⥤ CommAlgCat.{u} k) (c : Cocone F) (hc : IsColimit c)
    (ι : I → Type u) [∀ i, Finite (ι i)]
    (e : ∀ i, F.obj i ≅ CommAlgCat.of k (ι i → k)) :
    let T := Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap k c.pt))
    ∀ f : T ⟶ G, ∃ U : G.left.affineOpens,
      Set.range f.left.base ⊆ ((U : G.left.Opens) : Set G.left) := sorry

/-- Every finite family of rational points of a locally algebraic group scheme over an
algebraically closed field is contained in one affine open. -/
theorem exists_affineOpen_containing_rationalPoints {k : Type u} [Field k] [IsAlgClosed k]
    (G : SchemeOverField k) [GrpObj G] [LocallyAlgebraic G] {n : ℕ}
    (g : Fin n → (𝟙_ (SchemeOverField k) ⟶ G)) :
    ∃ U : G.left.affineOpens,
      Set.range (fun i ↦ (g i).left (IsLocalRing.closedPoint k)) ⊆
        ((U : G.left.Opens) : Set G.left) := sorry

end AlgebraicGeometry.GroupScheme
