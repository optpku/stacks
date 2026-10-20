module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison of brutal truncation tower presentations

The filtration-stage and `stupidTrunc` presentations of the brutal tower are
canonically isomorphic.  This leaf owns the naturality and functor-level
comparison API, together with the compatibility of the two canonical maps to
the source complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.CochainComplex.Brutal

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace Stage

namespace truncIso

/-- The arbitrary-cutoff brutal comparison is natural in a cochain-complex map. -/
@[reassoc, stacks 0D8Z "naturality of the arbitrary brutal truncation comparison"]
theorem naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (p : ℤ) :
    map f p ≫ (truncIso L p).hom =
      (truncIso K p).hom ≫
        HomologicalComplex.stupidTruncMap f (embeddingUpIntGE p) := sorry

/-- The inverse arbitrary-cutoff brutal comparison satisfies the reverse naturality square. -/
@[reassoc, stacks 0D8Z "inverse naturality of the arbitrary brutal truncation comparison"]
theorem inv_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (p : ℤ) :
    HomologicalComplex.stupidTruncMap f (embeddingUpIntGE p) ≫ (truncIso L p).inv =
      (truncIso K p).inv ≫ map f p := sorry

end truncIso

end Stage

namespace Tower

namespace truncIso

/-- The stage comparison is natural in a cochain-complex map. -/
@[reassoc, stacks 0D8Z "naturality of the brutal stage comparison"]
theorem naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    mapApp f n ≫ (truncIso L n).hom =
      (truncIso K n).hom ≫ Trunc.mapApp f n := sorry

/-- The inverse brutal stage comparison satisfies the reverse naturality square. -/
@[reassoc, stacks 0D8Z "inverse naturality of the brutal stage comparison"]
theorem inv_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    Trunc.mapApp f n ≫ (truncIso L n).inv =
      (truncIso K n).inv ≫ mapApp f n := sorry

/-- The stage comparison intertwines every morphism in the two brutal tower diagrams. -/
@[reassoc, stacks 0D8Z "diagram naturality of the brutal stage comparison"]
theorem diagram_naturality (K : CochainComplex A ℤ)
    {m n : ℕ} (f : m ⟶ n) :
    (diagram K).map f ≫ (truncIso K n).hom =
      (truncIso K m).hom ≫ (Trunc.diagram K).map f := sorry

/-- The inverse stage comparisons intertwine every morphism in the two brutal tower diagrams. -/
@[reassoc, stacks 0D8Z "inverse diagram naturality of the brutal stage comparison"]
theorem diagram_inv_naturality (K : CochainComplex A ℤ)
    {m n : ℕ} (f : m ⟶ n) :
    (Trunc.diagram K).map f ≫ (truncIso K n).inv =
      (truncIso K m).inv ≫ (diagram K).map f := sorry

end truncIso

/-- The two models of the brutal tower form canonically isomorphic diagrams. -/
@[stacks 0D8Z "comparison of filtration-stage and stupid-truncation brutal diagrams"]
noncomputable def diagramIso (K : CochainComplex A ℤ) :
    diagram K ≅ Trunc.diagram K :=
  NatIso.ofComponents (fun n ↦ truncIso K n)
    (fun {_ _} f ↦ truncIso.diagram_naturality K f)

namespace diagramIso

/-- A component of `diagramIso` is the canonical stage comparison. -/
@[simp, stacks 0D8Z "component of the brutal diagram comparison"]
theorem app (K : CochainComplex A ℤ) (n : ℕ) :
    (diagramIso K).app n = truncIso K n := sorry

/-- The forward component of `diagramIso` is the forward stage comparison. -/
@[simp, stacks 0D8Z "forward component of the brutal diagram comparison"]
theorem hom_app (K : CochainComplex A ℤ) (n : ℕ) :
    (diagramIso K).hom.app n = (truncIso K n).hom := sorry

/-- The inverse component of `diagramIso` is the inverse stage comparison. -/
@[simp, stacks 0D8Z "inverse component of the brutal diagram comparison"]
theorem inv_app (K : CochainComplex A ℤ) (n : ℕ) :
    (diagramIso K).inv.app n = (truncIso K n).inv := sorry

/-- The diagram comparison is natural in the cochain complex. -/
@[reassoc, stacks 0D8Z "naturality of the brutal diagram comparison"]
theorem naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    map f ≫ (diagramIso L).hom =
      (diagramIso K).hom ≫ Trunc.map f := sorry

/-- The inverse diagram comparison is natural in the cochain complex. -/
@[reassoc, stacks 0D8Z "inverse naturality of the brutal diagram comparison"]
theorem inv_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    Trunc.map f ≫ (diagramIso L).inv =
      (diagramIso K).inv ≫ map f := sorry

/-- The forward diagram comparison commutes with the canonical maps to the source complex. -/
@[reassoc, stacks 0D8Z "brutal diagram comparison and source transformation"]
theorem hom_comp_toConst (K : CochainComplex A ℤ) :
    (diagramIso K).hom ≫ Trunc.toConst K = toConst K := sorry

/-- The inverse diagram comparison commutes with the canonical maps to the source complex. -/
@[reassoc, stacks 0D8Z "inverse brutal diagram comparison and source transformation"]
theorem inv_comp_toConst (K : CochainComplex A ℤ) :
    (diagramIso K).inv ≫ toConst K = Trunc.toConst K := sorry

/-- At each tower index, the diagram comparison identifies the two cocone legs. -/
@[simp, reassoc, stacks 0D8Z "brutal diagram comparison on cocone legs"]
theorem hom_app_comp_cocone_ι_app (K : CochainComplex A ℤ) (n : ℕ) :
    (diagramIso K).hom.app n ≫ (Trunc.cocone K).ι.app n =
      (cocone K).ι.app n := sorry

/-- At each tower index, the forward diagram comparison identifies the two stage inclusions into
the source complex. -/
@[reassoc, stacks 0D8Z "brutal diagram comparison on stage inclusions"]
theorem hom_app_comp_ι (K : CochainComplex A ℤ) (n : ℕ) :
    (diagramIso K).hom.app n ≫ Trunc.ι K n = ι K n := sorry

/-- At each tower index, the inverse diagram comparison identifies the two stage inclusions into
the source complex. -/
@[reassoc, stacks 0D8Z "inverse brutal diagram comparison on stage inclusions"]
theorem inv_app_comp_ι (K : CochainComplex A ℤ) (n : ℕ) :
    (diagramIso K).inv.app n ≫ ι K n = Trunc.ι K n := sorry

end diagramIso

/-- The transported brutal tower functor is naturally isomorphic to the stupid-truncation tower
functor. -/
@[stacks 0D8Z "functor-level comparison of brutal tower presentations"]
noncomputable def functorIso :
    functor (A := A) ≅ Trunc.functor (A := A) :=
  NatIso.ofComponents (fun K ↦ diagramIso K)
    (fun {_ _} f ↦ diagramIso.naturality f)

namespace functorIso

/-- The forward functor comparison satisfies its naturality square. -/
@[reassoc, stacks 0D8Z "forward naturality of the brutal tower functor comparison"]
theorem hom_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (functor (A := A)).map f ≫ (functorIso (A := A)).hom.app L =
      (functorIso (A := A)).hom.app K ≫ (Trunc.functor (A := A)).map f := sorry

/-- The inverse functor comparison satisfies the reverse naturality square. -/
@[reassoc, stacks 0D8Z "inverse naturality of the brutal tower functor comparison"]
theorem inv_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (Trunc.functor (A := A)).map f ≫ (functorIso (A := A)).inv.app L =
      (functorIso (A := A)).inv.app K ≫ (functor (A := A)).map f := sorry

/-- A component of `functorIso` is the comparison of the corresponding tower diagrams. -/
@[simp, stacks 0D8Z "component of the brutal tower functor comparison"]
theorem app (K : CochainComplex A ℤ) :
    (functorIso (A := A)).app K = diagramIso K := sorry

/-- The forward component of `functorIso` is the forward diagram comparison. -/
@[simp, stacks 0D8Z "forward component of the brutal tower functor comparison"]
theorem hom_app (K : CochainComplex A ℤ) :
    (functorIso (A := A)).hom.app K = (diagramIso K).hom := sorry

/-- Evaluating the forward functor comparison at a tower index gives the forward stage
comparison. -/
@[simp, stacks 0D8Z "indexed forward component of the brutal tower functor comparison"]
theorem hom_app_app (K : CochainComplex A ℤ) (n : ℕ) :
    ((functorIso (A := A)).hom.app K).app n = (truncIso K n).hom := sorry

/-- The inverse component of `functorIso` is the inverse diagram comparison. -/
@[simp, stacks 0D8Z "inverse component of the brutal tower functor comparison"]
theorem inv_app (K : CochainComplex A ℤ) :
    (functorIso (A := A)).inv.app K = (diagramIso K).inv := sorry

/-- Evaluating the inverse functor comparison at a tower index gives the inverse stage comparison.
-/
@[simp, stacks 0D8Z "indexed inverse component of the brutal tower functor comparison"]
theorem inv_app_app (K : CochainComplex A ℤ) (n : ℕ) :
    ((functorIso (A := A)).inv.app K).app n = (truncIso K n).inv := sorry

/-- The forward functor comparison commutes with the canonical transformations to the source
complex. -/
@[reassoc, stacks 0D8Z "brutal tower functor comparison and source transformation"]
theorem hom_app_comp_toConst (K : CochainComplex A ℤ) :
    (functorIso (A := A)).hom.app K ≫ Trunc.toConst K = toConst K := sorry

/-- The inverse functor comparison commutes with the canonical transformations to the source
complex. -/
@[reassoc, stacks 0D8Z "inverse brutal tower functor comparison and source transformation"]
theorem inv_app_comp_toConst (K : CochainComplex A ℤ) :
    (functorIso (A := A)).inv.app K ≫ toConst K = Trunc.toConst K := sorry

end functorIso

end Tower

end CategoryTheory.CochainComplex.Brutal

end
