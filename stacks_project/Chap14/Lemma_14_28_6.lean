/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Homotopy
import StacksCheckRecall

/-!
@stack 01A0

# Source-facing bridge for Lemma 14.28.6

The alternating and normalized cochain functors carry product-free cosimplicial homotopies to
chain homotopies; the reusable statements are owned by their neutral ReasLib leaves.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

section Alternating

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasFiniteBiproducts A]
variable {U V : CosimplicialObject A} {a b : U ⟶ V}

/- Lemma 14.28.6 (1), directed companion: a chosen product-free homotopy gives a chosen
homotopy on alternating cochains. -/
#check (DeltaOneHomotopy.alternatingCoface (A := A) (a := a) :
  DeltaOneHomotopy a b →
    _root_.Homotopy
      ((alternatingCofaceMapComplex A).map a)
      ((alternatingCofaceMapComplex A).map b))

/- Lemma 14.28.6 (1): homotopic cosimplicial maps induce homotopic maps on alternating
cochains. The tagged source-facing form uses the cotensor relation; the preceding DeltaOne form
is the assumption-minimal generalization. -/
@[stacks 01A0 "Lemma 14.28.6 (1)"]
#check (Homotopic.alternatingCoface (A := A) (a := a) :
  Homotopic a b →
    homotopic A (ComplexShape.up ℕ)
      ((alternatingCofaceMapComplex A).map a)
      ((alternatingCofaceMapComplex A).map b))

end Alternating

section Normalized

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : CosimplicialObject A} {a b : U ⟶ V}

/- Lemma 14.28.6 (2), directed companion: a chosen product-free homotopy gives a chosen
homotopy on normalized cochains. -/
#check (DeltaOneHomotopy.normalizedCochain (A := A) (a := a) :
  DeltaOneHomotopy a b →
    _root_.Homotopy
      (normalizedCochainComplex.functor.map a)
      (normalizedCochainComplex.functor.map b))

/- Lemma 14.28.6 (2): homotopic cosimplicial maps induce homotopic maps on normalized
cochains. -/
@[stacks 01A0 "Lemma 14.28.6 (2)"]
#check (Homotopic.normalizedCochain (A := A) (a := a) :
  Homotopic a b →
    homotopic A (ComplexShape.up ℕ)
      (normalizedCochainComplex.functor.map a)
      (normalizedCochainComplex.functor.map b))

end Normalized

section Canonical

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : CosimplicialObject A} {a b : U ⟶ V}

/- Lemma 14.28.6: the canonical image quotient is the reusable normalized cochain target. -/
#check (DeltaOneHomotopy.degenerate.normalized (A := A) (a := a) :
  DeltaOneHomotopy a b →
    _root_.Homotopy
      ((DoldKan.degenerate.normalized.functor (A := A)).map a)
      ((DoldKan.degenerate.normalized.functor (A := A)).map b))

/- Lemma 14.28.6: homotopic maps land in the canonical normalized image homotopy relation. -/
#check (DeltaOneHomotopic.degenerate.normalized (A := A) (a := a) :
  DeltaOneHomotopic a b →
    homotopic A (ComplexShape.up ℕ)
      ((DoldKan.degenerate.normalized.functor (A := A)).map a)
      ((DoldKan.degenerate.normalized.functor (A := A)).map b))

/- The cotensor-valued source relation has the same canonical normalized-cochain image. -/
@[stacks 01A0 "Lemma 14.28.6: cotensor homotopy on normalized images"]
#check (Homotopic.degenerate.normalized (A := A) (a := a) :
  Homotopic a b →
    homotopic A (ComplexShape.up ℕ)
      ((DoldKan.degenerate.normalized.functor (A := A)).map a)
      ((DoldKan.degenerate.normalized.functor (A := A)).map b))

/- The canonical normalized image functor maps the whole product-free homotopy relation. -/
#check (homotopyRel.degenerate.normalized.isMappedBy (A := A) :
  HomRel.IsMappedBy (homotopyRel A)
    (DoldKan.degenerate.normalized.functor (A := A))
    (homotopic A (ComplexShape.up ℕ)))

end Canonical

end CategoryTheory.CosimplicialObject
