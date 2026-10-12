/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.KFlat
public import ReasLib.Algebra.Homology.HomologicalComplex.KFlat.Relative.Isomorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism transport for K-flat homological complexes

This file supplies the standard isomorphism-invariance API for shape-general monoidal
K-flatness.
@stack 06XZ
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace HomologicalComplex.IsKFlat

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C]
variable {I : Type w} [AddMonoid I] [DecidableEq I]
  {c : ComplexShape I} [c.TensorSigns]

/-- K-flatness transports from the source to the target of an isomorphism of homological
complexes. -/
theorem of_iso {K L : HomologicalComplex C c} (hK : K.IsKFlat) (e : K ≅ L) :
    L.IsKFlat := sorry

/-- Isomorphic homological complexes are simultaneously K-flat for the ambient monoidal tensor
product. -/
@[stacks 06XZ "isomorphism invariance of monoidal K-flatness"]
theorem iff_of_iso {K L : HomologicalComplex C c} (e : K ≅ L) :
    K.IsKFlat ↔ L.IsKFlat := sorry

end HomologicalComplex.IsKFlat
