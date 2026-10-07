module

public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Map.Zero
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Variable.Map.Preadditive

/-!
# Preadditive Maps of Projective Resolutions

This file exposes the dependent additive calculus for maps of projective resolutions through the
short, source-facing `ProjectiveResolution.Map` namespace.  The base cochain map changes under
addition, negation, and subtraction, so compatibility laws use explicit reindexing.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.ProjectiveResolution.Map

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

variable {K L M : CochainComplex 𝒜 ℤ} {f g : K ⟶ L} {h k : L ⟶ M}
  {P : ProjectiveResolution K} {Q : ProjectiveResolution L}
  {R : ProjectiveResolution M}

/-- Add two maps of projective resolutions, adding their base cochain maps. -/
abbrev add (m : Map f P Q) (n : Map g P Q) : Map (f + g) P Q :=
  Minus.TermsIn.QuasiIsoFrom.Map.add m n

/-- Addition of projective-resolution maps adds their model morphisms. -/
@[simp]
theorem add_modelHom (m : Map f P Q) (n : Map g P Q) :
    (add m n).modelHom = m.modelHom + n.modelHom := sorry

/-- Addition of projective-resolution maps adds their underlying cochain maps. -/
@[simp]
theorem add_hom (m : Map f P Q) (n : Map g P Q) :
    (add m n).hom = m.hom + n.hom := sorry

/-- The sum of projective-resolution maps satisfies the comparison square over the sum of their
base cochain maps. -/
@[reassoc]
theorem add_naturality (m : Map f P Q) (n : Map g P Q) :
    (add m n).hom ≫ Q.π = P.π ≫ (f + g) := sorry

/-- Negate a map of projective resolutions and its base cochain map. -/
abbrev neg (m : Map f P Q) : Map (-f) P Q :=
  Minus.TermsIn.QuasiIsoFrom.Map.neg m

/-- Negation of a projective-resolution map negates its model morphism. -/
@[simp]
theorem neg_modelHom (m : Map f P Q) : (neg m).modelHom = -m.modelHom := sorry

/-- Negation of a projective-resolution map negates its underlying cochain map. -/
@[simp]
theorem neg_hom (m : Map f P Q) : (neg m).hom = -m.hom := sorry

/-- A negated projective-resolution map satisfies the comparison square over the negated base
cochain map. -/
@[reassoc]
theorem neg_naturality (m : Map f P Q) :
    (neg m).hom ≫ Q.π = P.π ≫ (-f) := sorry

/-- Subtract two maps of projective resolutions, subtracting their base cochain maps. -/
abbrev sub (m : Map f P Q) (n : Map g P Q) : Map (f - g) P Q :=
  Minus.TermsIn.QuasiIsoFrom.Map.sub m n

/-- Subtraction of projective-resolution maps subtracts their model morphisms. -/
@[simp]
theorem sub_modelHom (m : Map f P Q) (n : Map g P Q) :
    (sub m n).modelHom = m.modelHom - n.modelHom := sorry

/-- Subtraction of projective-resolution maps subtracts their underlying cochain maps. -/
@[simp]
theorem sub_hom (m : Map f P Q) (n : Map g P Q) :
    (sub m n).hom = m.hom - n.hom := sorry

/-- The difference of projective-resolution maps satisfies the comparison square over the
difference of their base cochain maps. -/
@[reassoc]
theorem sub_naturality (m : Map f P Q) (n : Map g P Q) :
    (sub m n).hom ≫ Q.π = P.π ≫ (f - g) := sorry

/-- Reindexing commutes with addition of projective-resolution maps. -/
@[simp]
theorem reindex_add {f' g' : K ⟶ L} (ef : f = f') (eg : g = g')
    (m : Map f P Q) (n : Map g P Q) :
    reindex (congrArg₂ (fun (a b : K ⟶ L) ↦ a + b) ef eg) (add m n) =
      add (reindex ef m) (reindex eg n) := sorry

/-- Reindexing commutes with negation of projective-resolution maps. -/
@[simp]
theorem reindex_neg {f' : K ⟶ L} (e : f = f') (m : Map f P Q) :
    reindex (congrArg (fun a : K ⟶ L ↦ -a) e) (neg m) =
      neg (reindex e m) := sorry

/-- Reindexing commutes with subtraction of projective-resolution maps. -/
@[simp]
theorem reindex_sub {f' g' : K ⟶ L} (ef : f = f') (eg : g = g')
    (m : Map f P Q) (n : Map g P Q) :
    reindex (congrArg₂ (fun (a b : K ⟶ L) ↦ a - b) ef eg) (sub m n) =
      sub (reindex ef m) (reindex eg n) := sorry

/-- Composition distributes over addition in the left projective-resolution map. -/
@[simp]
theorem add_comp (m : Map f P Q) (n : Map g P Q) (q : Map h Q R) :
    reindex (Preadditive.add_comp K L M f g h) (comp (add m n) q) =
      add (comp m q) (comp n q) := sorry

/-- Composition distributes over addition in the right projective-resolution map. -/
@[simp]
theorem comp_add (m : Map f P Q) (n : Map h Q R) (q : Map k Q R) :
    reindex (Preadditive.comp_add K L M f h k) (comp m (add n q)) =
      add (comp m n) (comp m q) := sorry

/-- Composition commutes with negation in the left projective-resolution map. -/
@[simp]
theorem neg_comp (m : Map f P Q) (n : Map h Q R) :
    reindex (Preadditive.neg_comp f h) (comp (neg m) n) = neg (comp m n) := sorry

/-- Composition commutes with negation in the right projective-resolution map. -/
@[simp]
theorem comp_neg (m : Map f P Q) (n : Map h Q R) :
    reindex (Preadditive.comp_neg f h) (comp m (neg n)) = neg (comp m n) := sorry

/-- Composition distributes over subtraction in the left projective-resolution map. -/
@[simp]
theorem sub_comp (m : Map f P Q) (n : Map g P Q) (q : Map h Q R) :
    reindex (Preadditive.sub_comp f g h) (comp (sub m n) q) =
      sub (comp m q) (comp n q) := sorry

/-- Composition distributes over subtraction in the right projective-resolution map. -/
@[simp]
theorem comp_sub (m : Map f P Q) (n : Map h Q R) (q : Map k Q R) :
    reindex (Preadditive.comp_sub f h k) (comp m (sub n q)) =
      sub (comp m n) (comp m q) := sorry

end CochainComplex.ProjectiveResolution.Map
