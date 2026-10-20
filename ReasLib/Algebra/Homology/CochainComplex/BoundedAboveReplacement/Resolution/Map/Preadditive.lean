/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Map.Zero
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left.Map.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Preadditive Maps of Fixed-Upper-Bound Resolutions

This file specializes the dependent additive operations on neutral left-resolution maps. The
base cochain map changes with the operation, so the resulting family remains dependently typed.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom.Map

variable {A : Type u} [Category.{v} A] [Preadditive A] [CategoryWithHomology A]
  {P : ObjectProperty A} {a : ℤ}
  {K L : CochainComplex A ℤ} {f g : K ⟶ L}
  {R : QuasiIsoFrom P a K} {S : QuasiIsoFrom P a L}

/-- Add fixed-upper-bound resolution maps and their base cochain maps. -/
@[stacks 05T7 "addition of fixed-upper-bound resolution maps"]
abbrev add (m : Map f R S) (n : Map g R S) : Map (f + g) R S :=
  LocalizerMorphism.LeftResolution.Map.add m n

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
    (add m n).hom ≫ S.comparison = R.comparison ≫ (f + g) := sorry

/-- Negate a fixed-upper-bound resolution map and its base cochain map. -/
@[stacks 05T7 "negation of fixed-upper-bound resolution maps"]
abbrev neg (m : Map f R S) : Map (-f) R S :=
  LocalizerMorphism.LeftResolution.Map.neg m

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
    (neg m).hom ≫ S.comparison = R.comparison ≫ (-f) := sorry

/-- Subtract fixed-upper-bound resolution maps and their base cochain maps. -/
@[stacks 05T7 "subtraction of fixed-upper-bound resolution maps"]
abbrev sub (m : Map f R S) (n : Map g R S) : Map (f - g) R S :=
  LocalizerMorphism.LeftResolution.Map.sub m n

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
    (sub m n).hom ≫ S.comparison = R.comparison ≫ (f - g) := sorry

end CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom.Map


