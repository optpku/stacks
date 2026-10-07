module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.ModuleCat
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Functor
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Map
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.FiniteProjective
public import ReasLib.CategoryTheory.Monoidal.Closed.LaxMonoidal
public import ReasLib.CategoryTheory.Iso.Explicit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Scalar extension of module-valued Hom complexes

This leaf owns the canonical comparison obtained from the lax-monoidal structure on extension of
scalars.  The raw map is available without finiteness hypotheses; boundedness and finite
projectivity are hypotheses only on the `IsIso` upgrade.  Keeping those two layers separate lets
downstream arguments use the comparison map even when it is not invertible.

The closed module-complex instance used by this leaf is currently universe-aligned in Mathlib, so
the two module rings share `u`; the module-level flatness and arbitrary-ring-map relative leaves
below this layer remain universe-polymorphic.
@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CochainComplex.HomComplex

variable {A B : Type u} [CommRing A] [CommRing B]

namespace ScalarExtension

/-- Degreewise extension of scalars on integer cochain complexes. -/
@[stacks 0E1U "degreewise scalar extension of cochain complexes"]
abbrev functor (σ : A →+* B) :
    CochainComplex (ModuleCat A) ℤ ⥤ CochainComplex (ModuleCat B) ℤ :=
  Functor.Cochain.map (ModuleCat.extendScalars σ)

/-- The canonical map from the scalar extension of a module-valued Hom complex to the Hom complex
of the scalar-extended source and target. -/
@[stacks 0E1U "scalar-extension comparison for Hom complexes"]
noncomputable def comparison
    (σ : A →+* B) (P F : CochainComplex (ModuleCat A) ℤ) :
    (functor σ).obj (moduleComplex A P F) ⟶
      moduleComplex B ((functor σ).obj P) ((functor σ).obj F) :=
  (functor σ).map
      ((CategoryTheory.CochainComplex.InternalHom.moduleComplexIso P F).symm.hom) ≫
    Functor.LaxMonoidal.InternalHom.comparison (functor σ) P F ≫
      (CategoryTheory.CochainComplex.InternalHom.moduleComplexIso
        ((functor σ).obj P) ((functor σ).obj F)).hom

/-- The internal-Hom comparison before changing between the enriched and module-valued Hom
models. -/
@[stacks 0E1U "enriched scalar-extension comparison"]
noncomputable abbrev internalHomComparison
    (σ : A →+* B) (P F : CochainComplex (ModuleCat A) ℤ) :
    (functor σ).obj ((ihom P).obj F) ⟶
      (ihom ((functor σ).obj P)).obj ((functor σ).obj F) :=
  Functor.LaxMonoidal.InternalHom.comparison (functor σ) P F

/-- For a bounded-above termwise finite-projective source and a bounded-below target, scalar
extension commutes with the enriched internal Hom. -/
@[stacks 0E1U "finite-projective scalar-extension Hom isomorphism"]
theorem internalHomComparison_isIso
    (σ : A →+* B) (P F : CochainComplex (ModuleCat A) ℤ)
    (hP : CochainComplex.minus (ModuleCat A) P)
    (hPfp : P.IsTermwiseFiniteProjective)
    (hF : CochainComplex.plus (ModuleCat A) F) :
    IsIso (internalHomComparison σ P F) := sorry
/- Proof strategy: reduce to the finite support window, apply the tensor-Hom comparison for
finite-projective source components, and assemble the degreewise isomorphisms. -/

/-- The module-valued scalar-extension comparison is an isomorphism under the same finite-window
hypotheses. -/
@[stacks 0E1U "module-valued scalar-extension Hom isomorphism"]
theorem comparison_isIso
    (σ : A →+* B) (P F : CochainComplex (ModuleCat A) ℤ)
    (hP : CochainComplex.minus (ModuleCat A) P)
    (hPfp : P.IsTermwiseFiniteProjective)
    (hF : CochainComplex.plus (ModuleCat A) F) :
    IsIso (comparison σ P F) := by
  letI : IsIso (internalHomComparison σ P F) :=
    internalHomComparison_isIso σ P F hP hPfp hF
  dsimp only [comparison, internalHomComparison]
  infer_instance
/- Proof strategy: transport `internalHomComparison_isIso` across the two explicit
`moduleComplexIso` maps in `comparison`. -/

/-- The enriched scalar-extension comparison as an isomorphism, when an explicit invertibility
certificate is available.  The certificate is a data argument rather than a proof-local instance,
so downstream constructions can compose the comparison without rebuilding ambient typeclass state.
-/
@[stacks 0E1U "enriched scalar-extension Hom isomorphism"]
noncomputable def internalHomComparisonIso
    (σ : A →+* B) (P F : CochainComplex (ModuleCat A) ℤ)
    (h : IsIso (internalHomComparison σ P F)) :
    (functor σ).obj ((ihom P).obj F) ≅
      (ihom ((functor σ).obj P)).obj ((functor σ).obj F) :=
  CategoryTheory.IsIso.toIso h

/-- The forward map of `internalHomComparisonIso` is the canonical enriched comparison. -/
@[simp, stacks 0E1U "enriched scalar-extension Hom isomorphism forward map"]
theorem internalHomComparisonIso_hom
    (σ : A →+* B) (P F : CochainComplex (ModuleCat A) ℤ)
    (h : IsIso (internalHomComparison σ P F)) :
    (internalHomComparisonIso σ P F h).hom = internalHomComparison σ P F := rfl

/-- The enriched scalar-extension comparison is independent of the supplied invertibility proof. -/
@[stacks 0E1U "enriched scalar-extension Hom isomorphism proof independence"]
theorem internalHomComparisonIso_eq
    (σ : A →+* B) (P F : CochainComplex (ModuleCat A) ℤ)
    (h₁ h₂ : IsIso (internalHomComparison σ P F)) :
    internalHomComparisonIso σ P F h₁ = internalHomComparisonIso σ P F h₂ := by
  rfl

/- The finite-window specialization is the usual downstream entry point: it returns concrete
comparison data without asking callers to install the proposition-level `IsIso` result. -/
/-- The enriched scalar-extension Hom comparison as a concrete isomorphism for a finite-projective
source and a bounded-below target. -/
@[stacks 0E1U "finite-projective enriched scalar-extension Hom isomorphism"]
noncomputable def internalHomIso_of_finiteProjective
    (σ : A →+* B) (P F : CochainComplex (ModuleCat A) ℤ)
    (hP : CochainComplex.minus (ModuleCat A) P)
    (hPfp : P.IsTermwiseFiniteProjective)
    (hF : CochainComplex.plus (ModuleCat A) F) :
    (functor σ).obj ((ihom P).obj F) ≅
      (ihom ((functor σ).obj P)).obj ((functor σ).obj F) :=
  internalHomComparisonIso σ P F
    (internalHomComparison_isIso σ P F hP hPfp hF)

/-- The forward map of the finite-projective enriched scalar-extension isomorphism is the
canonical enriched comparison. -/
@[simp, stacks 0E1U "finite-projective enriched scalar-extension forward map"]
theorem internalHomIso_of_finiteProjective_hom
    (σ : A →+* B) (P F : CochainComplex (ModuleCat A) ℤ)
    (hP : CochainComplex.minus (ModuleCat A) P)
    (hPfp : P.IsTermwiseFiniteProjective)
    (hF : CochainComplex.plus (ModuleCat A) F) :
    (internalHomIso_of_finiteProjective σ P F hP hPfp hF).hom =
      internalHomComparison σ P F := rfl

/-- The module-valued scalar-extension comparison as an isomorphism, from an explicit
invertibility certificate. -/
@[stacks 0E1U "module-valued scalar-extension Hom isomorphism"]
noncomputable def comparisonIso
    (σ : A →+* B) (P F : CochainComplex (ModuleCat A) ℤ)
    (h : IsIso (comparison σ P F)) :
    (functor σ).obj (moduleComplex A P F) ≅
      moduleComplex B ((functor σ).obj P) ((functor σ).obj F) :=
  CategoryTheory.IsIso.toIso h

/-- The forward map of `comparisonIso` is the canonical module-valued comparison. -/
@[simp, stacks 0E1U "module-valued scalar-extension Hom isomorphism forward map"]
theorem comparisonIso_hom
    (σ : A →+* B) (P F : CochainComplex (ModuleCat A) ℤ)
    (h : IsIso (comparison σ P F)) :
    (comparisonIso σ P F h).hom = comparison σ P F := rfl

/-- The module-valued scalar-extension comparison is independent of the supplied invertibility
proof. -/
@[stacks 0E1U "module-valued scalar-extension Hom isomorphism proof independence"]
theorem comparisonIso_eq
    (σ : A →+* B) (P F : CochainComplex (ModuleCat A) ℤ)
    (h₁ h₂ : IsIso (comparison σ P F)) :
    comparisonIso σ P F h₁ = comparisonIso σ P F h₂ := by
  rfl

/-- The module-valued scalar-extension Hom comparison as a concrete isomorphism for a
finite-projective source and a bounded-below target. -/
@[stacks 0E1U "finite-projective module-valued scalar-extension Hom isomorphism"]
noncomputable def comparisonIso_of_finiteProjective
    (σ : A →+* B) (P F : CochainComplex (ModuleCat A) ℤ)
    (hP : CochainComplex.minus (ModuleCat A) P)
    (hPfp : P.IsTermwiseFiniteProjective)
    (hF : CochainComplex.plus (ModuleCat A) F) :
    (functor σ).obj (moduleComplex A P F) ≅
      moduleComplex B ((functor σ).obj P) ((functor σ).obj F) :=
  comparisonIso σ P F (comparison_isIso σ P F hP hPfp hF)

/-- The forward map of the finite-projective module-valued scalar-extension isomorphism is the
canonical module-valued comparison. -/
@[simp, stacks 0E1U "finite-projective scalar-extension forward map"]
theorem comparisonIso_of_finiteProjective_hom
    (σ : A →+* B) (P F : CochainComplex (ModuleCat A) ℤ)
    (hP : CochainComplex.minus (ModuleCat A) P)
    (hPfp : P.IsTermwiseFiniteProjective)
    (hF : CochainComplex.plus (ModuleCat A) F) :
    (comparisonIso_of_finiteProjective σ P F hP hPfp hF).hom =
      comparison σ P F := rfl

/-- Scalar extension preserves the bounded-below support of a module-valued cochain complex.
This is the Hom-complex-shaped bridge over the shape-independent `CochainComplex.plus_map` owner;
no finite-projective, flatness, or comparison-isomorphism hypothesis is needed. -/
@[stacks 0E1U "bounded-below scalar extension of a Hom complex"]
theorem plus
    (σ : A →+* B) {P F : CochainComplex (ModuleCat A) ℤ}
    (hE : CochainComplex.plus (ModuleCat A) (moduleComplex A P F)) :
    CochainComplex.plus (ModuleCat B) ((functor σ).obj (moduleComplex A P F)) :=
  CochainComplex.plus_map (ModuleCat.extendScalars σ) hE
/- Proof strategy: apply the shape-independent `CochainComplex.plus_map` theorem to the
extension-of-scalars functor and the supplied lower support witness. -/

end ScalarExtension

end CochainComplex.HomComplex
