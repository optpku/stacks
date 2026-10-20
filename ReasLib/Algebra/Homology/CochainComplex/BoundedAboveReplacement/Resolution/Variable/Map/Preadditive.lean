/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Variable.Map.Zero
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left.Map.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Preadditive Maps of Variable-Upper-Bound Resolutions

This file specializes the dependent preadditive calculus for maps of left resolutions to
variable-upper-bound termwise resolutions of cochain complexes.  The base cochain map changes
under addition, negation, and subtraction, so all compatibility laws retain their explicit
reindexing.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.Minus.TermsIn.QuasiIsoFrom.Map

variable {A : Type u} [Category.{v} A] [Preadditive A] [CategoryWithHomology A]
  {P : ObjectProperty A}

variable {K L M : CochainComplex A ℤ} {f g : K ⟶ L} {h k : L ⟶ M}
  {R : QuasiIsoFrom P K} {S : QuasiIsoFrom P L} {T : QuasiIsoFrom P M}

/-- Add two variable-upper-bound resolution maps, adding their base cochain maps. -/
@[stacks 05T7 "addition of variable-upper-bound resolution maps"]
abbrev add (m : Map f R S) (n : Map g R S) : Map (f + g) R S :=
  LocalizerMorphism.LeftResolution.Map.add m n

/-- Addition of variable-upper-bound resolution maps adds their bundled model morphisms. -/
@[simp]
theorem add_modelHom (m : Map f R S) (n : Map g R S) :
    (add m n).modelHom = m.modelHom + n.modelHom := sorry

/-- Addition of variable-upper-bound resolution maps adds their underlying cochain maps. -/
@[simp]
theorem add_hom (m : Map f R S) (n : Map g R S) :
    (add m n).hom = m.hom + n.hom := sorry

/-- The sum of two variable-upper-bound resolution maps satisfies the comparison square over
the sum of their base cochain maps. -/
@[reassoc]
theorem add_naturality (m : Map f R S) (n : Map g R S) :
    (add m n).hom ≫ S.comparison = R.comparison ≫ (f + g) := sorry

/-- Negate a variable-upper-bound resolution map and its base cochain map. -/
@[stacks 05T7 "negation of variable-upper-bound resolution maps"]
abbrev neg (m : Map f R S) : Map (-f) R S :=
  LocalizerMorphism.LeftResolution.Map.neg m

/-- Negation of a variable-upper-bound resolution map negates its bundled model morphism. -/
@[simp]
theorem neg_modelHom (m : Map f R S) : (neg m).modelHom = -m.modelHom := sorry

/-- Negation of a variable-upper-bound resolution map negates its underlying cochain map. -/
@[simp]
theorem neg_hom (m : Map f R S) : (neg m).hom = -m.hom := sorry

/-- A negated variable-upper-bound resolution map satisfies the comparison square over the
negated base cochain map. -/
@[reassoc]
theorem neg_naturality (m : Map f R S) :
    (neg m).hom ≫ S.comparison = R.comparison ≫ (-f) := sorry

/-- Subtract two variable-upper-bound resolution maps and their base cochain maps. -/
@[stacks 05T7 "subtraction of variable-upper-bound resolution maps"]
abbrev sub (m : Map f R S) (n : Map g R S) : Map (f - g) R S :=
  LocalizerMorphism.LeftResolution.Map.sub m n

/-- Subtraction of variable-upper-bound resolution maps subtracts their bundled model
morphisms. -/
@[simp]
theorem sub_modelHom (m : Map f R S) (n : Map g R S) :
    (sub m n).modelHom = m.modelHom - n.modelHom := sorry

/-- Subtraction of variable-upper-bound resolution maps subtracts their underlying cochain
maps. -/
@[simp]
theorem sub_hom (m : Map f R S) (n : Map g R S) :
    (sub m n).hom = m.hom - n.hom := sorry

/-- The difference of two variable-upper-bound resolution maps satisfies the comparison square
over the difference of their base cochain maps. -/
@[reassoc]
theorem sub_naturality (m : Map f R S) (n : Map g R S) :
    (sub m n).hom ≫ S.comparison = R.comparison ≫ (f - g) := sorry

/-- Reindexing commutes with addition of variable-upper-bound resolution maps. -/
@[simp]
theorem reindex_add {f' g' : K ⟶ L} (ef : f = f') (eg : g = g')
    (m : Map f R S) (n : Map g R S) :
    reindex (congrArg₂ (fun (a b : K ⟶ L) ↦ a + b) ef eg) (add m n) =
      add (reindex ef m) (reindex eg n) := sorry

/-- Reindexing commutes with negation of variable-upper-bound resolution maps. -/
@[simp]
theorem reindex_neg {f' : K ⟶ L} (e : f = f') (m : Map f R S) :
    reindex (congrArg (fun a : K ⟶ L ↦ -a) e) (neg m) =
      neg (reindex e m) := sorry

/-- Reindexing commutes with subtraction of variable-upper-bound resolution maps. -/
@[simp]
theorem reindex_sub {f' g' : K ⟶ L} (ef : f = f') (eg : g = g')
    (m : Map f R S) (n : Map g R S) :
    reindex (congrArg₂ (fun (a b : K ⟶ L) ↦ a - b) ef eg) (sub m n) =
      sub (reindex ef m) (reindex eg n) := sorry

/-- Composition distributes over addition in the left variable-upper-bound resolution map. -/
@[simp]
theorem add_comp (m : Map f R S) (n : Map g R S) (q : Map h S T) :
    reindex (Preadditive.add_comp K L M f g h) (comp (add m n) q) =
      add (comp m q) (comp n q) := sorry

/-- Composition distributes over addition in the right variable-upper-bound resolution map. -/
@[simp]
theorem comp_add (m : Map f R S) (n : Map h S T) (q : Map k S T) :
    reindex (Preadditive.comp_add K L M f h k) (comp m (add n q)) =
      add (comp m n) (comp m q) := sorry

/-- Composition commutes with negation in the left variable-upper-bound resolution map. -/
@[simp]
theorem neg_comp (m : Map f R S) (n : Map h S T) :
    reindex (Preadditive.neg_comp f h) (comp (neg m) n) = neg (comp m n) := sorry

/-- Composition commutes with negation in the right variable-upper-bound resolution map. -/
@[simp]
theorem comp_neg (m : Map f R S) (n : Map h S T) :
    reindex (Preadditive.comp_neg f h) (comp m (neg n)) = neg (comp m n) := sorry

/-- Composition distributes over subtraction in the left variable-upper-bound resolution map. -/
@[simp]
theorem sub_comp (m : Map f R S) (n : Map g R S) (q : Map h S T) :
    reindex (Preadditive.sub_comp f g h) (comp (sub m n) q) =
      sub (comp m q) (comp n q) := sorry

/-- Composition distributes over subtraction in the right variable-upper-bound resolution map. -/
@[simp]
theorem comp_sub (m : Map f R S) (n : Map h S T) (q : Map k S T) :
    reindex (Preadditive.comp_sub f h k) (comp m (sub n q)) =
      sub (comp m n) (comp m q) := sorry

end CochainComplex.Minus.TermsIn.QuasiIsoFrom.Map


