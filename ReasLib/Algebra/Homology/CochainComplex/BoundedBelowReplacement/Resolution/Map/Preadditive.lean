/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Map.Zero
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Right.Map.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Preadditive Maps of Fixed-Lower-Bound Resolutions

This file specializes the dependent additive operations on neutral right-resolution maps. The
base cochain map changes with the operation, so the resulting family remains dependently typed.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo.Map

variable {A : Type u} [Category.{v} A] [Preadditive A] [CategoryWithHomology A]
  {P : ObjectProperty A} {a : ℤ}
  {K L : CochainComplex A ℤ} {f g : K ⟶ L}
  {R : QuasiIsoTo P a K} {S : QuasiIsoTo P a L}

/-- Add fixed-lower-bound resolution maps and their base cochain maps. -/
@[stacks 05T6 "addition of fixed-lower-bound resolution maps"]
abbrev add (m : Map f R S) (n : Map g R S) : Map (f + g) R S :=
  LocalizerMorphism.RightResolution.Map.add m n

/-- The sum of fixed-bound resolution maps adds their model morphisms. -/
@[simp]
theorem add_modelHom (m : Map f R S) (n : Map g R S) :
    (add m n).modelHom = m.modelHom + n.modelHom := sorry

/-- The sum of fixed-bound resolution maps adds their underlying cochain maps. -/
@[simp]
theorem add_hom (m : Map f R S) (n : Map g R S) :
    (add m n).hom = m.hom + n.hom := sorry

/-- The sum of fixed-bound resolution maps satisfies the comparison square over the sum of the
base cochain maps. -/
@[reassoc]
theorem add_naturality (m : Map f R S) (n : Map g R S) :
    R.comparison ≫ (add m n).hom = (f + g) ≫ S.comparison := sorry

/-- Negate a fixed-lower-bound resolution map and its base cochain map. -/
@[stacks 05T6 "negation of fixed-lower-bound resolution maps"]
abbrev neg (m : Map f R S) : Map (-f) R S :=
  LocalizerMorphism.RightResolution.Map.neg m

/-- Negation of a fixed-bound resolution map negates its model morphism. -/
@[simp]
theorem neg_modelHom (m : Map f R S) : (neg m).modelHom = -m.modelHom := sorry

/-- Negation of a fixed-bound resolution map negates its underlying cochain map. -/
@[simp]
theorem neg_hom (m : Map f R S) : (neg m).hom = -m.hom := sorry

/-- A negated fixed-bound resolution map satisfies the comparison square over the negated base
cochain map. -/
@[reassoc]
theorem neg_naturality (m : Map f R S) :
    R.comparison ≫ (neg m).hom = (-f) ≫ S.comparison := sorry

/-- Subtract fixed-lower-bound resolution maps and their base cochain maps. -/
@[stacks 05T6 "subtraction of fixed-lower-bound resolution maps"]
abbrev sub (m : Map f R S) (n : Map g R S) : Map (f - g) R S :=
  LocalizerMorphism.RightResolution.Map.sub m n

/-- The difference of fixed-bound resolution maps subtracts their model morphisms. -/
@[simp]
theorem sub_modelHom (m : Map f R S) (n : Map g R S) :
    (sub m n).modelHom = m.modelHom - n.modelHom := sorry

/-- The difference of fixed-bound resolution maps subtracts their underlying cochain maps. -/
@[simp]
theorem sub_hom (m : Map f R S) (n : Map g R S) :
    (sub m n).hom = m.hom - n.hom := sorry

/-- The difference of fixed-bound resolution maps satisfies the comparison square over the
difference of the base cochain maps. -/
@[reassoc]
theorem sub_naturality (m : Map f R S) (n : Map g R S) :
    R.comparison ≫ (sub m n).hom = (f - g) ≫ S.comparison := sorry

end CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo.Map


