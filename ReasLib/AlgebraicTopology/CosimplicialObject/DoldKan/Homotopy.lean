/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.Homotopy.Whisker
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Normalized.Quotient
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.Normalized
public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.AlternatingCoface
public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.DeltaOne.Comparison
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Cosimplicial homotopies on normalized cochains

Normalized cochains carry product-free cosimplicial homotopies to chain homotopies.  This is the
abelian, quotient-defined companion to the preadditive alternating-coface result.

@stack 01A0
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicTopology
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : CosimplicialObject A} {a b : U ⟶ V}

namespace homotopyRel.normalizedCochain

/-- The normalized cochain complex functor maps product-free cosimplicial homotopy into cochain
homotopy. -/
@[stacks 01A0 "normalized-cochain functor maps homotopy relations"]
instance isMappedBy :
    HomRel.IsMappedBy (homotopyRel A) normalizedCochainComplex.functor
      (homotopic A (ComplexShape.up ℕ)) := sorry

end homotopyRel.normalizedCochain

namespace normalizedCochainComplex

/-- The normalized-cochain map induced by a cosimplicial morphism factors through the
alternating-coface map using the canonical section and quotient. -/
@[reassoc, stacks 01A0 "normalized-cochain factorization through alternating cofaces"]
theorem map_eq_factorization (f : U ⟶ V) :
    normalizedCochainComplex.functor.map f =
      ι U ≫ (alternatingCofaceMapComplex A).map f ≫ π V := sorry

end normalizedCochainComplex

namespace DeltaOneHomotopy

/-- A product-free `Δ[1]`-homotopy induces a concrete homotopy between the corresponding maps
of normalized cochain complexes. -/
@[stacks 01A0 "directed homotopy on normalized cochains"]
noncomputable def normalizedCochain (H : DeltaOneHomotopy a b) :
    _root_.Homotopy
      (normalizedCochainComplex.functor.map a)
      (normalizedCochainComplex.functor.map b) :=
  _root_.Homotopy.ofSplitMono
    (normalizedCochainComplex.ι.splitMono (A := A)) H.alternatingCoface

namespace normalizedCochain

/-- The degree-`(n + 1, n)` component of the induced normalized-cochain homotopy is obtained by
restricting the corresponding alternating-coface component along the canonical retract. -/
@[stacks 01A0 "normalized-cochain homotopy component"]
theorem hom (H : DeltaOneHomotopy a b) (n : ℕ) :
    H.normalizedCochain.hom (n + 1) n =
      (normalizedCochainComplex.ι U).f (n + 1) ≫
        H.alternatingCoface.hom (n + 1) n ≫
          (normalizedCochainComplex.π V).f n := sorry

end normalizedCochain

end DeltaOneHomotopy

/-- Product-free `Δ[1]`-homotopic cosimplicial morphisms induce the canonical chain-homotopy
relation on normalized cochain complexes. -/
@[stacks 01A0 "homotopic maps on normalized cochains"]
theorem DeltaOneHomotopic.normalizedCochain (h : DeltaOneHomotopic a b) :
    homotopic A (ComplexShape.up ℕ)
      (normalizedCochainComplex.functor.map a)
      (normalizedCochainComplex.functor.map b) := sorry

/-- Under an available `Δ[1]` cotensor, normalized cochains preserve the source-facing
cotensor-valued cosimplicial homotopy relation. -/
@[stacks 01A0 "cotensor homotopy on normalized cochains"]
theorem Homotopic.normalizedCochain
    {b : U ⟶ V} [HasCotensor (Δ[1] : SSet.{0}) V]
    (h : Homotopic a b) :
    homotopic A (ComplexShape.up ℕ)
      (normalizedCochainComplex.functor.map a)
      (normalizedCochainComplex.functor.map b) := sorry

section Canonical

namespace homotopyRel.degenerate.normalized

/-- The canonical normalized image functor maps product-free cosimplicial homotopy into cochain
homotopy. -/
@[stacks 01A0 "canonical normalized image functor maps homotopy relations"]
instance isMappedBy :
    HomRel.IsMappedBy (homotopyRel A)
      (DoldKan.degenerate.normalized.functor (A := A))
      (homotopic A (ComplexShape.up ℕ)) := sorry

end homotopyRel.degenerate.normalized

namespace DeltaOneHomotopy.degenerate

/-- A directed product-free cosimplicial homotopy induces a homotopy on the canonical normalized
image quotient. -/
@[stacks 01A0 "directed homotopy on canonical normalized images"]
noncomputable def normalized (H : DeltaOneHomotopy a b) :
    _root_.Homotopy
      ((DoldKan.degenerate.normalized.functor (A := A)).map a)
      ((DoldKan.degenerate.normalized.functor (A := A)).map b) :=
  _root_.Homotopy.ofSplitMono
    (DoldKan.degenerate.normalized.ι.splitMono (A := A)) H.alternatingCoface

end DeltaOneHomotopy.degenerate

namespace DeltaOneHomotopy.degenerate.normalized

/-- The degree-`(n + 1, n)` component of the canonical normalized image homotopy. -/
@[stacks 01A0 "canonical normalized image homotopy component"]
theorem hom (H : DeltaOneHomotopy a b) (n : ℕ) :
    (DeltaOneHomotopy.degenerate.normalized H).hom (n + 1) n =
      (DoldKan.degenerate.normalized.ι (A := A) U).f (n + 1) ≫
        H.alternatingCoface.hom (n + 1) n ≫
          (DoldKan.degenerate.normalized.π (A := A) V).f n := sorry

end DeltaOneHomotopy.degenerate.normalized

namespace DeltaOneHomotopic.degenerate

/-- The canonical normalized image functor sends product-free homotopic maps to cochain-homotopic
maps. -/
@[stacks 01A0 "homotopic maps on canonical normalized images"]
theorem normalized (h : DeltaOneHomotopic a b) :
    homotopic A (ComplexShape.up ℕ)
      ((DoldKan.degenerate.normalized.functor (A := A)).map a)
      ((DoldKan.degenerate.normalized.functor (A := A)).map b) := sorry

end DeltaOneHomotopic.degenerate

namespace Homotopic.degenerate

/-- The canonical normalized image functor also preserves cotensor-valued cosimplicial homotopy
whenever the target cotensor exists. -/
@[stacks 01A0 "cotensor homotopy on canonical normalized images"]
theorem normalized
    {b : U ⟶ V} [HasCotensor (Δ[1] : SSet.{0}) V]
    (h : Homotopic a b) :
    homotopic A (ComplexShape.up ℕ)
      ((DoldKan.degenerate.normalized.functor (A := A)).map a)
      ((DoldKan.degenerate.normalized.functor (A := A)).map b) := sorry

end Homotopic.degenerate

end Canonical

end CategoryTheory.CosimplicialObject
