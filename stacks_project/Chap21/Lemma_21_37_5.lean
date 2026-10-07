module

public import ReasLib.CategoryTheory.Sites.Derived.SectionsComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.InverseImageComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.UnderlyingSectionsComparison
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.37.5

Let `u : 𝒞 ⥤ 𝒟` be continuous and cocontinuous, let `g : Sh(𝒞) ⟶ Sh(𝒟)` be the
corresponding morphism of topoi, and let `U : 𝒞`.  Stacks 0DD8 has two independent clauses:

1. for a derived abelian sheaf `M : DerivedCategory (Sheaf JD AddCommGrpCat)`, the objects
   `RΓ(U, (siteAbelianInverseImageDerived JC JD u).obj M)` and
   `RΓ(u.obj U, M)` are isomorphic;
2. for `R : Sheaf JD RingCat` and
   `M : ModuleDerived (moduleInverseImage.target R)`, the objects obtained by applying
   `moduleInverseImage.derived u R` and taking derived sections over `U` and `u.obj U` are
   isomorphic.  Thus the source ring sheaf is represented by
   `moduleInverseImage.source u R`, rather than by an unbundled module inverse-image notation.

The canonical abelian root is the natural isomorphism
`SiteAbelianSectionsDerived.inverseImageNatIsoOfPreservesInjectives`; `inverseImageIso` is only its
Prop-valued compatibility view.  The explicit `PreservesInjectiveObjects` binder is a derived-model
certificate: a concrete site adjunction must discharge it through an exact-left-adjoint bridge,
and it is not silently added to the source statement.  The module clause uses the
continuous-presentation owner `RingedSite.Cocontinuous.moduleInverseImage`; it does not manufacture
a `RingedSite.Hom`, which would impose representable flatness absent from the source.  Its exact
and total-derived models are related by a named isomorphism, while objectwise sections use the
canonical underlying-additive derived-sections bridge.
-/

open CategoryTheory

/- Lemma 21.37.5 (0DD8) (1): abelian inverse image and derived sections. -/
@[stacks 0DD8 "(1), abelian inverse image and sections"]
#check @CategoryTheory.SiteAbelianSectionsDerived.inverseImageNatIsoOfPreservesInjectives

@[stacks 0DD8 "(1), canonical abelian object component"]
#check @CategoryTheory.SiteAbelianSectionsDerived.inverseImageObjIsoOfPreservesInjectives

@[stacks 0DD8 "(1), abelian inverse image and sections Prop view"]
#check @CategoryTheory.SiteAbelianSectionsDerived.inverseImageIso

@[stacks 0DD8 "(1), abelian derived inverse-image owner"]
#check @CategoryTheory.siteAbelianInverseImageDerived

@[stacks 0DD8 "(1), abelian derived-sections owner"]
#check @CategoryTheory.siteAbelianSectionsDerived

/- Lemma 21.37.5 (0DD8) (2): module inverse image and derived sections. -/
@[stacks 0DD8 "(2), module inverse image and sections"]
#check @RingedSite.Cocontinuous.moduleInverseImage.sectionsIso

@[stacks 0DD8 "(2), derived module inverse-image owner"]
#check @RingedSite.Cocontinuous.moduleInverseImage.derived

@[stacks 0DD8 "(2), total-to-exact module derived transport"]
#check @RingedSite.Cocontinuous.moduleInverseImage.totalDerivedIso

@[stacks 0DD8 "(2), underlying additive derived-sections owner"]
#check @RingedSite.Hom.ModuleSections.Underlying.sectionsDerived

/- The following maps are infrastructure for the module clause: they compare module sections
with their underlying additive sections and are not a second source-facing theorem. -/
@[stacks 0DD8 "(2), underlying additive sections comparison"]
#check @RingedSite.Hom.ModuleSections.sectionsIso

@[stacks 0DD8 "(2), underlying additive sections comparison map"]
#check @RingedSite.Hom.ModuleSections.sectionsComparison

@[stacks 0DD8 "(2), underlying additive comparison component"]
#check @RingedSite.Hom.ModuleSections.sectionsAppIso

@[stacks 0DD8 "(2), underlying additive comparison specification"]
#check @RingedSite.Hom.ModuleSections.sectionsComparison_fac_app
