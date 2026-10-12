/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable.Map.Zero
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Right.Map.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Preadditive Maps of Variable-Lower-Bound Resolutions

This file specializes the dependent preadditive calculus for maps of right resolutions to
variable-lower-bound termwise resolutions of cochain complexes.  The base cochain map changes
under addition, negation, and subtraction, so all compatibility laws retain their explicit
reindexing.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.Plus.TermsIn.QuasiIsoTo.Map

variable {A : Type u} [Category.{v} A] [Preadditive A] [CategoryWithHomology A]
  {P : ObjectProperty A}

variable {K L M : CochainComplex A ℤ} {f g : K ⟶ L} {h k : L ⟶ M}
  {R : QuasiIsoTo P K} {S : QuasiIsoTo P L} {T : QuasiIsoTo P M}

/-- Add two variable-lower-bound resolution maps, adding their base cochain maps. -/
@[stacks 05T6 "addition of variable-lower-bound resolution maps"]
abbrev add (m : Map f R S) (n : Map g R S) : Map (f + g) R S :=
  LocalizerMorphism.RightResolution.Map.add m n

/-- Addition of variable-lower-bound resolution maps adds their bundled model morphisms. -/
@[simp]
theorem add_modelHom (m : Map f R S) (n : Map g R S) :
    (add m n).modelHom = m.modelHom + n.modelHom := sorry

/-- Addition of variable-lower-bound resolution maps adds their underlying cochain maps. -/
@[simp]
theorem add_hom (m : Map f R S) (n : Map g R S) :
    (add m n).hom = m.hom + n.hom := sorry

/-- The sum of two variable-lower-bound resolution maps satisfies the comparison square over
the sum of their base cochain maps. -/
@[reassoc]
theorem add_naturality (m : Map f R S) (n : Map g R S) :
    R.comparison ≫ (add m n).hom = (f + g) ≫ S.comparison := sorry

/-- Negate a variable-lower-bound resolution map and its base cochain map. -/
@[stacks 05T6 "negation of variable-lower-bound resolution maps"]
abbrev neg (m : Map f R S) : Map (-f) R S :=
  LocalizerMorphism.RightResolution.Map.neg m

/-- Negation of a variable-lower-bound resolution map negates its bundled model morphism. -/
@[simp]
theorem neg_modelHom (m : Map f R S) : (neg m).modelHom = -m.modelHom := sorry

/-- Negation of a variable-lower-bound resolution map negates its underlying cochain map. -/
@[simp]
theorem neg_hom (m : Map f R S) : (neg m).hom = -m.hom := sorry

/-- A negated variable-lower-bound resolution map satisfies the comparison square over the
negated base cochain map. -/
@[reassoc]
theorem neg_naturality (m : Map f R S) :
    R.comparison ≫ (neg m).hom = (-f) ≫ S.comparison := sorry

/-- Subtract two variable-lower-bound resolution maps and their base cochain maps. -/
@[stacks 05T6 "subtraction of variable-lower-bound resolution maps"]
abbrev sub (m : Map f R S) (n : Map g R S) : Map (f - g) R S :=
  LocalizerMorphism.RightResolution.Map.sub m n

/-- Subtraction of variable-lower-bound resolution maps subtracts their bundled model
morphisms. -/
@[simp]
theorem sub_modelHom (m : Map f R S) (n : Map g R S) :
    (sub m n).modelHom = m.modelHom - n.modelHom := sorry

/-- Subtraction of variable-lower-bound resolution maps subtracts their underlying cochain
maps. -/
@[simp]
theorem sub_hom (m : Map f R S) (n : Map g R S) :
    (sub m n).hom = m.hom - n.hom := sorry

/-- The difference of two variable-lower-bound resolution maps satisfies the comparison square
over the difference of their base cochain maps. -/
@[reassoc]
theorem sub_naturality (m : Map f R S) (n : Map g R S) :
    R.comparison ≫ (sub m n).hom = (f - g) ≫ S.comparison := sorry

/-- Reindexing commutes with addition of variable-lower-bound resolution maps. -/
@[simp]
theorem reindex_add {f' g' : K ⟶ L} (ef : f = f') (eg : g = g')
    (m : Map f R S) (n : Map g R S) :
    reindex (congrArg₂ (fun (a b : K ⟶ L) ↦ a + b) ef eg) (add m n) =
      add (reindex ef m) (reindex eg n) := sorry

/-- Reindexing commutes with negation of variable-lower-bound resolution maps. -/
@[simp]
theorem reindex_neg {f' : K ⟶ L} (e : f = f') (m : Map f R S) :
    reindex (congrArg (fun a : K ⟶ L ↦ -a) e) (neg m) =
      neg (reindex e m) := sorry

/-- Reindexing commutes with subtraction of variable-lower-bound resolution maps. -/
@[simp]
theorem reindex_sub {f' g' : K ⟶ L} (ef : f = f') (eg : g = g')
    (m : Map f R S) (n : Map g R S) :
    reindex (congrArg₂ (fun (a b : K ⟶ L) ↦ a - b) ef eg) (sub m n) =
      sub (reindex ef m) (reindex eg n) := sorry

/-- Composition distributes over addition in the left variable-lower-bound resolution map. -/
@[simp]
theorem add_comp (m : Map f R S) (n : Map g R S) (q : Map h S T) :
    reindex (Preadditive.add_comp K L M f g h) (comp (add m n) q) =
      add (comp m q) (comp n q) := sorry

/-- Composition distributes over addition in the right variable-lower-bound resolution map. -/
@[simp]
theorem comp_add (m : Map f R S) (n : Map h S T) (q : Map k S T) :
    reindex (Preadditive.comp_add K L M f h k) (comp m (add n q)) =
      add (comp m n) (comp m q) := sorry

/-- Composition commutes with negation in the left variable-lower-bound resolution map. -/
@[simp]
theorem neg_comp (m : Map f R S) (n : Map h S T) :
    reindex (Preadditive.neg_comp f h) (comp (neg m) n) = neg (comp m n) := sorry

/-- Composition commutes with negation in the right variable-lower-bound resolution map. -/
@[simp]
theorem comp_neg (m : Map f R S) (n : Map h S T) :
    reindex (Preadditive.comp_neg f h) (comp m (neg n)) = neg (comp m n) := sorry

/-- Composition distributes over subtraction in the left variable-lower-bound resolution map. -/
@[simp]
theorem sub_comp (m : Map f R S) (n : Map g R S) (q : Map h S T) :
    reindex (Preadditive.sub_comp f g h) (comp (sub m n) q) =
      sub (comp m q) (comp n q) := sorry

/-- Composition distributes over subtraction in the right variable-lower-bound resolution map. -/
@[simp]
theorem comp_sub (m : Map f R S) (n : Map h S T) (q : Map k S T) :
    reindex (Preadditive.comp_sub f h k) (comp m (sub n q)) =
      sub (comp m n) (comp m q) := sorry

end CochainComplex.Plus.TermsIn.QuasiIsoTo.Map


