/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Definition

@[expose] public section

/-!
# Constructing Telescope Presentations

This leaf turns a distinguished telescope triangle on an explicitly supplied
coproduct cocone into a concrete `HomotopyColimit.Presentation`. A final
compatibility constructor specializes this API to the coproduct selected by a
`HasCoproduct` instance.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

noncomputable section

namespace CategoryTheory.HomotopyColimit

open Limits.Sequential

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]

/-- Build a telescope presentation from a distinguished triangle on an explicitly supplied
coproduct cocone. -/
@[stacks 090Z]
def Presentation.ofTriangle {K : ℕ ⥤ D} {X : D}
    (coproduct : ColimitCocone (Discrete.functor K.obj))
    (toCocone : coproduct.cocone.pt ⟶ X)
    (connecting : X ⟶ coproduct.cocone.pt⟦(1 : ℤ)⟧)
    (h_triangle : Triangle.mk (CoproductCocone.telescopeMap K coproduct)
      toCocone connecting ∈ distTriang D) : Presentation K X where
  coproduct := coproduct
  toCocone := toCocone
  connecting := connecting
  distinguished := h_triangle

/-- `Presentation.ofTriangle` stores the supplied coproduct cocone. -/
@[simp]
theorem Presentation.ofTriangle.coproduct {K : ℕ ⥤ D} {X : D}
    (coproduct : ColimitCocone (Discrete.functor K.obj))
    (toCocone : coproduct.cocone.pt ⟶ X)
    (connecting : X ⟶ coproduct.cocone.pt⟦(1 : ℤ)⟧)
    (h_triangle : Triangle.mk (CoproductCocone.telescopeMap K coproduct)
      toCocone connecting ∈ distTriang D) :
    (Presentation.ofTriangle coproduct toCocone connecting h_triangle).coproduct =
      coproduct := sorry

/-- `Presentation.ofTriangle` stores the supplied coproduct-to-cocone map. -/
@[simp]
theorem Presentation.ofTriangle.toCocone {K : ℕ ⥤ D} {X : D}
    (coproduct : ColimitCocone (Discrete.functor K.obj))
    (toCocone : coproduct.cocone.pt ⟶ X)
    (connecting : X ⟶ coproduct.cocone.pt⟦(1 : ℤ)⟧)
    (h_triangle : Triangle.mk (CoproductCocone.telescopeMap K coproduct)
      toCocone connecting ∈ distTriang D) :
    (Presentation.ofTriangle coproduct toCocone connecting h_triangle).toCocone =
      toCocone := sorry

/-- `Presentation.ofTriangle` stores the supplied connecting morphism. -/
@[simp]
theorem Presentation.ofTriangle.connecting {K : ℕ ⥤ D} {X : D}
    (coproduct : ColimitCocone (Discrete.functor K.obj))
    (toCocone : coproduct.cocone.pt ⟶ X)
    (connecting : X ⟶ coproduct.cocone.pt⟦(1 : ℤ)⟧)
    (h_triangle : Triangle.mk (CoproductCocone.telescopeMap K coproduct)
      toCocone connecting ∈ distTriang D) :
    (Presentation.ofTriangle coproduct toCocone connecting h_triangle).connecting =
      connecting := sorry

/-- Build a telescope presentation from compatible stage legs on an explicitly supplied
coproduct cocone. -/
@[stacks 090Z]
def Presentation.ofLegs {K : ℕ ⥤ D} {X : D}
    (coproduct : ColimitCocone (Discrete.functor K.obj))
    (ι : ∀ n, K.obj n ⟶ X)
    (connecting : X ⟶ coproduct.cocone.pt⟦(1 : ℤ)⟧)
    (h_triangle : Triangle.mk (CoproductCocone.telescopeMap K coproduct)
      (CoproductCocone.desc coproduct ι) connecting ∈ distTriang D) : Presentation K X :=
  Presentation.ofTriangle coproduct (CoproductCocone.desc coproduct ι)
    connecting h_triangle

/-- `Presentation.ofLegs` stores the supplied coproduct cocone. -/
@[simp]
theorem Presentation.ofLegs.coproduct {K : ℕ ⥤ D} {X : D}
    (coproduct : ColimitCocone (Discrete.functor K.obj))
    (ι : ∀ n, K.obj n ⟶ X)
    (connecting : X ⟶ coproduct.cocone.pt⟦(1 : ℤ)⟧)
    (h_triangle : Triangle.mk (CoproductCocone.telescopeMap K coproduct)
      (CoproductCocone.desc coproduct ι) connecting ∈ distTriang D) :
    (Presentation.ofLegs coproduct ι connecting h_triangle).coproduct = coproduct := sorry

/-- The coproduct-to-cocone map of `Presentation.ofLegs` is induced by the supplied stage
maps. -/
@[simp]
theorem Presentation.ofLegs.toCocone {K : ℕ ⥤ D} {X : D}
    (coproduct : ColimitCocone (Discrete.functor K.obj))
    (ι : ∀ n, K.obj n ⟶ X)
    (connecting : X ⟶ coproduct.cocone.pt⟦(1 : ℤ)⟧)
    (h_triangle : Triangle.mk (CoproductCocone.telescopeMap K coproduct)
      (CoproductCocone.desc coproduct ι) connecting ∈ distTriang D) :
    (Presentation.ofLegs coproduct ι connecting h_triangle).toCocone =
      CoproductCocone.desc coproduct ι := sorry

/-- `Presentation.ofLegs` stores the supplied connecting morphism. -/
@[simp]
theorem Presentation.ofLegs.connecting {K : ℕ ⥤ D} {X : D}
    (coproduct : ColimitCocone (Discrete.functor K.obj))
    (ι : ∀ n, K.obj n ⟶ X)
    (connecting : X ⟶ coproduct.cocone.pt⟦(1 : ℤ)⟧)
    (h_triangle : Triangle.mk (CoproductCocone.telescopeMap K coproduct)
      (CoproductCocone.desc coproduct ι) connecting ∈ distTriang D) :
    (Presentation.ofLegs coproduct ι connecting h_triangle).connecting = connecting := sorry

/-- The stage maps of `Presentation.ofLegs` are the supplied family. -/
@[simp]
theorem Presentation.ofLegs.ι {K : ℕ ⥤ D} {X : D}
    (coproduct : ColimitCocone (Discrete.functor K.obj))
    (ι : ∀ n, K.obj n ⟶ X)
    (connecting : X ⟶ coproduct.cocone.pt⟦(1 : ℤ)⟧)
    (h_triangle : Triangle.mk (CoproductCocone.telescopeMap K coproduct)
      (CoproductCocone.desc coproduct ι) connecting ∈ distTriang D) (n : ℕ) :
    (Presentation.ofLegs coproduct ι connecting h_triangle).ι n = ι n := sorry

/-- Reinterpret a distinguished telescope triangle on the coproduct selected by a
`HasCoproduct` instance as a triangle on its explicit colimit cocone. -/
theorem Presentation.ofCoproductTriangle.distinguished
    {K : ℕ ⥤ D} [HasCoproduct K.obj] {X : D}
    (toCocone : ∐ K.obj ⟶ X) (connecting : X ⟶ (∐ K.obj)⟦(1 : ℤ)⟧)
    (h_triangle : Triangle.mk (Limits.Sequential.telescopeMap K)
      toCocone connecting ∈ distTriang D) :
    Triangle.mk (CoproductCocone.telescopeMap K
      (getColimitCocone (Discrete.functor K.obj)))
      toCocone connecting ∈ distTriang D := sorry

/-- Compatibility constructor for a telescope triangle on the coproduct selected by a
`HasCoproduct` instance. -/
def Presentation.ofCoproductTriangle {K : ℕ ⥤ D} [HasCoproduct K.obj] {X : D}
    (toCocone : ∐ K.obj ⟶ X) (connecting : X ⟶ (∐ K.obj)⟦(1 : ℤ)⟧)
    (h_triangle : Triangle.mk (Limits.Sequential.telescopeMap K)
      toCocone connecting ∈ distTriang D) : Presentation K X :=
  Presentation.ofTriangle (getColimitCocone (Discrete.functor K.obj))
    toCocone connecting
    (Presentation.ofCoproductTriangle.distinguished toCocone connecting h_triangle)

/-- The explicit coproduct of `Presentation.ofCoproductTriangle` is the cocone selected by
the ambient coproduct instance. -/
@[simp]
theorem Presentation.ofCoproductTriangle.coproduct
    {K : ℕ ⥤ D} [HasCoproduct K.obj] {X : D}
    (toCocone : ∐ K.obj ⟶ X) (connecting : X ⟶ (∐ K.obj)⟦(1 : ℤ)⟧)
    (h_triangle : Triangle.mk (Limits.Sequential.telescopeMap K)
      toCocone connecting ∈ distTriang D) :
    (Presentation.ofCoproductTriangle toCocone connecting h_triangle).coproduct =
      getColimitCocone (Discrete.functor K.obj) := sorry

/-- The coproduct-to-cocone map recovered from `Presentation.ofCoproductTriangle` is the
supplied map. -/
@[simp]
theorem Presentation.ofCoproductTriangle.toCocone
    {K : ℕ ⥤ D} [HasCoproduct K.obj] {X : D}
    (toCocone : ∐ K.obj ⟶ X) (connecting : X ⟶ (∐ K.obj)⟦(1 : ℤ)⟧)
    (h_triangle : Triangle.mk (Limits.Sequential.telescopeMap K)
      toCocone connecting ∈ distTriang D) :
    (Presentation.ofCoproductTriangle toCocone connecting h_triangle).toCocone =
      toCocone := sorry

/-- The connecting morphism recovered from `Presentation.ofCoproductTriangle` is the
supplied map. -/
@[simp]
theorem Presentation.ofCoproductTriangle.connecting
    {K : ℕ ⥤ D} [HasCoproduct K.obj] {X : D}
    (toCocone : ∐ K.obj ⟶ X) (connecting : X ⟶ (∐ K.obj)⟦(1 : ℤ)⟧)
    (h_triangle : Triangle.mk (Limits.Sequential.telescopeMap K)
      toCocone connecting ∈ distTriang D) :
    (Presentation.ofCoproductTriangle toCocone connecting h_triangle).connecting =
      connecting := sorry

/-- The `n`th leg of `Presentation.ofCoproductTriangle` is the selected coproduct inclusion
followed by the supplied map. -/
@[simp]
theorem Presentation.ofCoproductTriangle.ι
    {K : ℕ ⥤ D} [HasCoproduct K.obj] {X : D}
    (toCocone : ∐ K.obj ⟶ X) (connecting : X ⟶ (∐ K.obj)⟦(1 : ℤ)⟧)
    (h_triangle : Triangle.mk (Limits.Sequential.telescopeMap K)
      toCocone connecting ∈ distTriang D) (n : ℕ) :
    (Presentation.ofCoproductTriangle toCocone connecting h_triangle).ι n =
      Limits.Sigma.ι K.obj n ≫ toCocone := sorry

end CategoryTheory.HomotopyColimit
