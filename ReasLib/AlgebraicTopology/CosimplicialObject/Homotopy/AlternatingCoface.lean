module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.Equiv
public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.DeltaOne.Comparison
public import ReasLib.AlgebraicTopology.SimplicialSet.StdSimplexOne
public import ReasLib.Algebra.Homology.Homotopy.Equiv
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Alternating coface complexes and cosimplicial homotopy equivalences

This module records that the alternating coface map complex carries product-free cosimplicial
homotopy equivalences to chain homotopy equivalences. It deliberately depends only on the
preadditive cosimplicial infrastructure, not on the opposite-simplicial or Dold--Kan bridges.
-/

@[expose] public section

open CategoryTheory
open AlgebraicTopology
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A] [Preadditive A]
variable {U V : CosimplicialObject A} {a : U ⟶ V}

namespace homotopyRel.alternatingCoface

/-- The alternating-coface complex functor maps product-free cosimplicial homotopy into cochain
homotopy. -/
@[stacks 01A0 "alternating-coface functor maps homotopy relations"]
instance isMappedBy :
    HomRel.IsMappedBy (homotopyRel A) (alternatingCofaceMapComplex A)
      (homotopic A (ComplexShape.up ℕ)) := sorry

end homotopyRel.alternatingCoface

namespace DeltaOneHomotopy

namespace alternatingCoface

/-- The component family underlying the alternating-coface homotopy induced by a product-free
`Δ[1]`-homotopy. It is supported in bidegrees `(n + 1, n)` and uses the source sign convention
`(-1) ^ (i + 1)`. -/
@[stacks 01A0 "alternating-coface homotopy components"]
noncomputable def components {b : U ⟶ V} (H : DeltaOneHomotopy a b) (p q : ℕ) :
    U.obj (SimplexCategory.mk p) ⟶ V.obj (SimplexCategory.mk q) :=
  if hpq : q + 1 = p then
    eqToHom (congrArg (fun n : ℕ ↦ U.obj (SimplexCategory.mk n)) hpq).symm ≫
      ∑ i : Fin (q + 1), ((-1 : ℤ) ^ ((i : ℕ) + 1)) •
        (H.hom (SSet.stdSimplex.objMk₁ i.succ.castSucc) ≫ V.map (SimplexCategory.σ i))
  else 0

/-- The alternating-coface component family vanishes away from the relation of the cochain
complex shape. -/
@[stacks 01A0 "alternating-coface component support"]
theorem zero {b : U ⟶ V} (H : DeltaOneHomotopy a b) :
    ∀ p q, ¬(ComplexShape.up ℕ).Rel q p → components H p q = 0 := sorry

/-- The alternating-coface component family satisfies the cochain-homotopy equation. -/
@[stacks 01A0 "alternating-coface component equation"]
theorem comm {b : U ⟶ V} (H : DeltaOneHomotopy a b) :
    ∀ n, ((alternatingCofaceMapComplex A).map a).f n =
      dNext (C := (alternatingCofaceMapComplex A).obj U)
          (D := (alternatingCofaceMapComplex A).obj V) n (components H) +
        prevD (C := (alternatingCofaceMapComplex A).obj U)
          (D := (alternatingCofaceMapComplex A).obj V) n (components H) +
        ((alternatingCofaceMapComplex A).map b).f n := sorry

end alternatingCoface

/-- A product-free `Δ[1]`-homotopy induces a concrete homotopy between the corresponding maps
of alternating coface complexes. -/
@[stacks 01A0 "directed homotopy on alternating cochains"]
noncomputable def alternatingCoface {b : U ⟶ V} (H : DeltaOneHomotopy a b) :
    _root_.Homotopy
      ((alternatingCofaceMapComplex A).map a)
      ((alternatingCofaceMapComplex A).map b) where
  hom := alternatingCoface.components H
  zero := alternatingCoface.zero H
  comm := alternatingCoface.comm H

namespace alternatingCoface

/-- The degree-`(n + 1, n)` component of the alternating-coface homotopy is the alternating sum
of the product-free homotopy components followed by the codegeneracy maps of the target. -/
@[stacks 01A0 "alternating-coface homotopy component formula"]
theorem hom {b : U ⟶ V} (H : DeltaOneHomotopy a b) (n : ℕ) :
    H.alternatingCoface.hom (n + 1) n =
      ∑ i : Fin (n + 1), ((-1 : ℤ) ^ ((i : ℕ) + 1)) •
        (H.hom (SSet.stdSimplex.objMk₁ i.succ.castSucc) ≫
          V.map (SimplexCategory.σ i)) := sorry

/-- Every component of the alternating-coface homotopy outside bidegrees `(n + 1, n)` is zero. -/
@[simp, stacks 01A0 "alternating-coface homotopy component support"]
theorem hom_eq_zero {b : U ⟶ V} (H : DeltaOneHomotopy a b)
    (p q : ℕ) (hpq : q + 1 ≠ p) :
    H.alternatingCoface.hom p q = 0 := sorry

end alternatingCoface

end DeltaOneHomotopy

/-- The alternating-coface complex functor preserves the full morphism property of product-free
cosimplicial homotopy equivalences. -/
@[stacks 0FKK "alternating-coface functor preserves homotopy equivalences"]
theorem homotopyEquivalences.alternatingCoface :
    homotopyEquivalences A ≤
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ)).inverseImage
        (alternatingCofaceMapComplex A) := sorry

namespace DeltaOneHomotopic

/-- Lemma 14.28.6 (1): product-free `Δ[1]`-homotopic morphisms of cosimplicial objects induce
the canonical chain-homotopy relation on alternating coface map complexes. -/
@[stacks 01A0 "homotopic maps on alternating cochains"]
theorem alternatingCoface
    {b : U ⟶ V} (h : DeltaOneHomotopic a b) :
    homotopic A (ComplexShape.up ℕ)
      ((alternatingCofaceMapComplex A).map a)
      ((alternatingCofaceMapComplex A).map b) := sorry

end DeltaOneHomotopic

namespace Homotopic

/-- Under an available `Δ[1]` cotensor, the alternating-coface functor also preserves the
cotensor-valued cosimplicial homotopy relation. The product-free theorem remains the core API. -/
@[stacks 01A0 "cotensor homotopy on alternating cochains"]
theorem alternatingCoface
    {b : U ⟶ V} [HasCotensor (Δ[1] : SSet.{0}) V] (h : Homotopic a b) :
    homotopic A (ComplexShape.up ℕ)
      ((alternatingCofaceMapComplex A).map a)
      ((alternatingCofaceMapComplex A).map b) := sorry

end Homotopic

namespace HomotopyEquiv

/-- The alternating-coface complex of a product-free cosimplicial homotopy equivalence,
retaining the image of its chosen inverse. -/
@[stacks 0FKK "structured alternating-coface homotopy equivalence"]
noncomputable def alternatingCoface (e : HomotopyEquiv U V) :
    HomRel.Equiv (homotopic A (ComplexShape.up ℕ))
      ((alternatingCofaceMapComplex A).obj U) ((alternatingCofaceMapComplex A).obj V) :=
  e.map (alternatingCofaceMapComplex A)

namespace alternatingCoface

/-- The forward map of the alternating-coface image is induced by the original forward
morphism. -/
@[simp, stacks 0FKK "alternating-coface homotopy-equivalence forward map"]
theorem hom (e : HomotopyEquiv U V) :
    e.alternatingCoface.hom = (alternatingCofaceMapComplex A).map e.hom := sorry

/-- The chosen inverse of the alternating-coface image is induced by the original chosen
inverse. -/
@[simp, stacks 0FKK "alternating-coface homotopy-equivalence inverse map"]
theorem inv (e : HomotopyEquiv U V) :
    e.alternatingCoface.inv = (alternatingCofaceMapComplex A).map e.inv := sorry

/-- The alternating coface map complex sends a product-free cosimplicial homotopy equivalence to
a chain homotopy equivalence. -/
@[stacks 0FKK "alternating cochains preserve homotopy equivalences"]
theorem isHomotopyEquivalence (e : HomotopyEquiv U V) :
    HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ)
      ((alternatingCofaceMapComplex A).map e.hom) := sorry

end alternatingCoface

end HomotopyEquiv

/-- Lemma 14.28.7 (1): if `a` is a product-free homotopy equivalence of cosimplicial objects,
then its induced map on alternating coface map complexes is a homotopy equivalence of cochain
complexes. -/
@[stacks 0FKK "alternating cochains preserve homotopy equivalences"]
theorem IsHomotopyEquivalence.alternatingCoface
    (ha : IsHomotopyEquivalence a) :
    HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ)
      ((alternatingCofaceMapComplex A).map a) := sorry

end CategoryTheory.CosimplicialObject
