/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero

@[expose] public section

open AlgebraicGeometry CategoryTheory GrothendieckTopology

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.Etale

/-- For a separated finite-type scheme of dimension at most one over an algebraically
closed field, a short exact sequence of module sheaves has finite degree-`q` étale
cohomology in the middle whenever it does at both endpoints. -/
theorem finiteCohomologyOfShortExact
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    {k : Type v} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1)
    (q : ℕ)
    {F₁ F F₂ : Sheaf X.left.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ)}
    (i : F₁ ⟶ F) (p : F ⟶ F₂) (h_ip : i ≫ p = 0)
    (h_sheaf : (ShortComplex.mk i p h_ip).ShortExact)
    [HasWeakSheafify X.left.smallEtaleTopology
      (ModuleCat.{max u (v + 1)} Λ)]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)}]
    [HasExt (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)})]
    [X.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)]
    [Module.Finite Λ
      ((siteModuleCohomologyModuleFunctor
        (J := X.left.smallEtaleTopology) (A := Λ) q).obj F₁)]
    [Module.Finite Λ
      ((siteModuleCohomologyModuleFunctor
        (J := X.left.smallEtaleTopology) (A := Λ) q).obj F₂)] :
    Module.Finite Λ
      ((siteModuleCohomologyModuleFunctor
        (J := X.left.smallEtaleTopology) (A := Λ) q).obj F) := sorry

/-- On a separated finite-type scheme of dimension at most one over an algebraically
closed field, a constructible sheaf of modules over a Noetherian ring has finite
degree-`q` étale cohomology if and only if its restriction to a dense open subscheme,
extended by zero, has finite degree-`q` étale cohomology. -/
theorem finiteCohomology_iff_extensionByZero
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    {k : Type v} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1)
    {X' : Scheme.{v}} (j : X' ⟶ X.left) [IsOpenImmersion j]
    (h_dense : Dense (Set.range j.base)) (q : ℕ)
    [∀ Y : Scheme.{v}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ)]
    [∀ (Y : Scheme.{v}) (U : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{max u (v + 1)} Λ)]
    [∀ (Y : Scheme.{v}) (f : Y ⟶ X.left)
      (P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{max u (v + 1)} Λ),
      (smallEtalePullback f).op.HasLeftKanExtension P]
    [∀ P : X'.Etaleᵒᵖ ⥤ ModuleCat.{max u (v + 1)} Λ,
      (etaleRestriction j).op.HasLeftKanExtension P]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)}]
    [HasExt (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)})]
    [X.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ))
    (hF : CategoryTheory.Sheaf.IsConstructibleEtale
      (fun {Y} f => ((smallEtalePullback f).sheafPullback
        (ModuleCat.{max u (v + 1)} Λ) X.left.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G => CategoryTheory.Sheaf.IsLocallyConstantWith
        (fun M : ModuleCat.{max u (v + 1)} Λ => Module.Finite Λ M) G) F) :
    Module.Finite Λ
      ((siteModuleCohomologyModuleFunctor (J := X.left.smallEtaleTopology) (A := Λ) q).obj F) ↔
    Module.Finite Λ
        ((siteModuleCohomologyModuleFunctor (J := X.left.smallEtaleTopology) (A := Λ) q).obj
          ((etaleExtensionByZero j (ModuleCat.{max u (v + 1)} Λ)).obj
            ((etaleRestrictionSheaf j (ModuleCat.{max u (v + 1)} Λ)).obj F))) := sorry

/-- A finite morphism of separated finite-type schemes over an algebraically closed field
of dimension at most one preserves finiteness of étale cohomology for module sheaves. -/
theorem finiteCohomologyOfFinitePushforward
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    {k : Type v} [Field k] [IsAlgClosed k]
    (X Y : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom] [Scheme.Hom.FiniteType Y.hom]
    [IsSeparated X.hom] [IsSeparated Y.hom]
    (f : X.left ⟶ Y.left) [IsFinite f] (h_over : f ≫ Y.hom = X.hom)
    (hX : topologicalKrullDim X.left ≤ 1)
    (hY : topologicalKrullDim Y.left ≤ 1)
    (q : ℕ) (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ))
    [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ)]
    [HasWeakSheafify Y.left.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ)]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)}]
    [HasSheafify Y.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)}]
    [HasExt (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)})]
    [HasExt (Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)})]
    [X.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)]
    [Y.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)]
    [Module.Finite Λ
      ((siteModuleCohomologyModuleFunctor
        (J := X.left.smallEtaleTopology) (A := Λ) q).obj F)] :
    Module.Finite Λ
      ((siteModuleCohomologyModuleFunctor
        (J := Y.left.smallEtaleTopology) (A := Λ) q).obj
          (((smallEtalePullback f).sheafPushforwardContinuous
              (ModuleCat.{max u (v + 1)} Λ)
              Y.left.smallEtaleTopology X.left.smallEtaleTopology).obj F)) := sorry

end AlgebraicGeometry.Scheme.Etale
