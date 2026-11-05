module

public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution.Map.Zero
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable.Map.Preadditive

/-!
# Preadditive Maps of Injective Resolutions

This file exposes the dependent additive calculus for maps of injective resolutions through the
short, source-facing `InjectiveResolution.Map` namespace.  The base cochain map changes under
addition, negation, and subtraction, so compatibility laws use explicit reindexing.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.InjectiveResolution.Map

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

variable {K L M : CochainComplex 𝒜 ℤ} {f g : K ⟶ L} {h k : L ⟶ M}
  {I : InjectiveResolution K} {J : InjectiveResolution L}
  {H : InjectiveResolution M}

/-- Add two maps of injective resolutions, adding their base cochain maps. -/
abbrev add (m : Map f I J) (n : Map g I J) : Map (f + g) I J :=
  Plus.TermsIn.QuasiIsoTo.Map.add m n

/-- Addition of injective-resolution maps adds their model morphisms. -/
@[simp]
theorem add_modelHom (m : Map f I J) (n : Map g I J) :
    (add m n).modelHom = m.modelHom + n.modelHom := sorry

/-- Addition of injective-resolution maps adds their underlying cochain maps. -/
@[simp]
theorem add_hom (m : Map f I J) (n : Map g I J) :
    (add m n).hom = m.hom + n.hom := sorry

/-- The sum of injective-resolution maps satisfies the comparison square over the sum of their
base cochain maps. -/
@[reassoc]
theorem add_naturality (m : Map f I J) (n : Map g I J) :
    I.ι ≫ (add m n).hom = (f + g) ≫ J.ι := sorry

/-- Negate a map of injective resolutions and its base cochain map. -/
abbrev neg (m : Map f I J) : Map (-f) I J :=
  Plus.TermsIn.QuasiIsoTo.Map.neg m

/-- Negation of an injective-resolution map negates its model morphism. -/
@[simp]
theorem neg_modelHom (m : Map f I J) : (neg m).modelHom = -m.modelHom := sorry

/-- Negation of an injective-resolution map negates its underlying cochain map. -/
@[simp]
theorem neg_hom (m : Map f I J) : (neg m).hom = -m.hom := sorry

/-- A negated injective-resolution map satisfies the comparison square over the negated base
cochain map. -/
@[reassoc]
theorem neg_naturality (m : Map f I J) :
    I.ι ≫ (neg m).hom = (-f) ≫ J.ι := sorry

/-- Subtract two maps of injective resolutions, subtracting their base cochain maps. -/
abbrev sub (m : Map f I J) (n : Map g I J) : Map (f - g) I J :=
  Plus.TermsIn.QuasiIsoTo.Map.sub m n

/-- Subtraction of injective-resolution maps subtracts their model morphisms. -/
@[simp]
theorem sub_modelHom (m : Map f I J) (n : Map g I J) :
    (sub m n).modelHom = m.modelHom - n.modelHom := sorry

/-- Subtraction of injective-resolution maps subtracts their underlying cochain maps. -/
@[simp]
theorem sub_hom (m : Map f I J) (n : Map g I J) :
    (sub m n).hom = m.hom - n.hom := sorry

/-- The difference of injective-resolution maps satisfies the comparison square over the
difference of their base cochain maps. -/
@[reassoc]
theorem sub_naturality (m : Map f I J) (n : Map g I J) :
    I.ι ≫ (sub m n).hom = (f - g) ≫ J.ι := sorry

/-- Reindexing commutes with addition of injective-resolution maps. -/
@[simp]
theorem reindex_add {f' g' : K ⟶ L} (ef : f = f') (eg : g = g')
    (m : Map f I J) (n : Map g I J) :
    reindex (congrArg₂ (fun (a b : K ⟶ L) ↦ a + b) ef eg) (add m n) =
      add (reindex ef m) (reindex eg n) := sorry

/-- Reindexing commutes with negation of injective-resolution maps. -/
@[simp]
theorem reindex_neg {f' : K ⟶ L} (e : f = f') (m : Map f I J) :
    reindex (congrArg (fun a : K ⟶ L ↦ -a) e) (neg m) =
      neg (reindex e m) := sorry

/-- Reindexing commutes with subtraction of injective-resolution maps. -/
@[simp]
theorem reindex_sub {f' g' : K ⟶ L} (ef : f = f') (eg : g = g')
    (m : Map f I J) (n : Map g I J) :
    reindex (congrArg₂ (fun (a b : K ⟶ L) ↦ a - b) ef eg) (sub m n) =
      sub (reindex ef m) (reindex eg n) := sorry

/-- Composition distributes over addition in the left injective-resolution map. -/
@[simp]
theorem add_comp (m : Map f I J) (n : Map g I J) (q : Map h J H) :
    reindex (Preadditive.add_comp K L M f g h) (comp (add m n) q) =
      add (comp m q) (comp n q) := sorry

/-- Composition distributes over addition in the right injective-resolution map. -/
@[simp]
theorem comp_add (m : Map f I J) (n : Map h J H) (q : Map k J H) :
    reindex (Preadditive.comp_add K L M f h k) (comp m (add n q)) =
      add (comp m n) (comp m q) := sorry

/-- Composition commutes with negation in the left injective-resolution map. -/
@[simp]
theorem neg_comp (m : Map f I J) (n : Map h J H) :
    reindex (Preadditive.neg_comp f h) (comp (neg m) n) = neg (comp m n) := sorry

/-- Composition commutes with negation in the right injective-resolution map. -/
@[simp]
theorem comp_neg (m : Map f I J) (n : Map h J H) :
    reindex (Preadditive.comp_neg f h) (comp m (neg n)) = neg (comp m n) := sorry

/-- Composition distributes over subtraction in the left injective-resolution map. -/
@[simp]
theorem sub_comp (m : Map f I J) (n : Map g I J) (q : Map h J H) :
    reindex (Preadditive.sub_comp f g h) (comp (sub m n) q) =
      sub (comp m q) (comp n q) := sorry

/-- Composition distributes over subtraction in the right injective-resolution map. -/
@[simp]
theorem comp_sub (m : Map f I J) (n : Map h J H) (q : Map k J H) :
    reindex (Preadditive.comp_sub f h k) (comp m (sub n q)) =
      sub (comp m n) (comp m q) := sorry

end CochainComplex.InjectiveResolution.Map


