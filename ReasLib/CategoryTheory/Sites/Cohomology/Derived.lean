module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.Sites.AbelianSheaf
public import ReasLib.CategoryTheory.Sites.Cohomology.Presheaf
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import ReasLib.CategoryTheory.Sites.GlobalSections.Additive
public import ReasLib.CategoryTheory.Sites.Cohomology.Presheaf.Derived

/-!
# Derived Global Sections and Sheaf Cohomology

This compatibility leaf owns the site-generic comparison between derived global sections and
sheaf cohomology.  Derived cohomology over an arbitrary presheaf lives in the more precise
`Cohomology.Presheaf.Derived` leaf, which is re-exported here.
@stack 091A
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]

/-- The degree-zero Ext functor from the constant integer sheaf, written as an additive functor
value on a sheaf. -/
@[stacks 071E "degree-zero global sections and Ext bridge"]
noncomputable abbrev globalSectionsExtZeroEquiv
    (F : Sheaf J AddCommGrpCat.{w}) :
    (Γ J AddCommGrpCat.{w}).obj F ≃+
      (Abelian.extFunctorObj (constantIntegerSheaf J) 0).obj F :=
  (globalSectionsAddEquivConstantIntegerSheafHomOnSite J F).trans
    Abelian.Ext.addEquiv₀.symm

/-- The degree-zero global-sections/Ext comparison is natural in the coefficient sheaf. -/
@[stacks 071E "naturality of the global sections and Ext bridge"]
theorem globalSectionsExtZeroEquiv_naturality
    {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) :
    (Γ J AddCommGrpCat.{w}).map f ≫
        (globalSectionsExtZeroEquiv J G).toAddCommGrpIso.hom =
      (globalSectionsExtZeroEquiv J F).toAddCommGrpIso.hom ≫
        (Abelian.extFunctorObj (constantIntegerSheaf J) 0).map f := sorry

/-- The natural isomorphism identifying global sections with degree-zero `Ext` from the constant
integer sheaf. -/
@[stacks 071E "global sections as degree-zero Ext"]
noncomputable def globalSectionsNatIsoExtZero :
    Γ J AddCommGrpCat.{w} ≅
      Abelian.extFunctorObj (constantIntegerSheaf J) 0 :=
  NatIso.ofComponents
    (fun F ↦ (globalSectionsExtZeroEquiv J F).toAddCommGrpIso)
    (fun f ↦ globalSectionsExtZeroEquiv_naturality J f)

variable [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{w})]

/-- The ordinary right-derived functors of global sections are the canonical sheaf-cohomology
functors on any site satisfying the required existence hypotheses. -/
@[stacks 091A]
theorem rightDerivedGlobalSections_isIsomorphic_functorH (p : ℕ) :
    IsIsomorphic
      ((Γ J AddCommGrpCat.{w}).rightDerived p)
      (functorH J p) := sorry

/-- A chosen injective resolution computes global sheaf cohomology by applying global sections
degreewise and taking homology. -/
@[stacks 071E "global sheaf cohomology from an injective resolution"]
theorem globalCohomology_isomorphic_homology_of_injectiveResolution
    (F : Sheaf J AddCommGrpCat.{w}) (I : InjectiveResolution F) (p : ℕ) :
    IsIsomorphic ((functorH J p).obj F)
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
        (ComplexShape.up ℕ) p).obj
          (((Γ J AddCommGrpCat.{w}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex)) := sorry

end CategoryTheory.Sheaf
