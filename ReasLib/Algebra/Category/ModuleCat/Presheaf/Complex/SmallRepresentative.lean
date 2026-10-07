module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Complex.SmallSubcomplex
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Small representatives in the derived category of presheaf modules

The size of a derived object is the least section-cardinality of a representing cochain complex.
This file records the resulting small-representative theorem using an actual subobject of any
chosen representative.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace CategoryTheory.PresheafOfModules.Cochain

variable {C : Type u} [Category.{v} C]
variable (O : Cᵒᵖ ⥤ RingCat.{w})
variable [HasDerivedCategory (PresheafOfModules.{z} O)]

/-- The least section-cardinality among cochain complexes representing a derived object. -/
@[stacks 0GYY "cardinality of a derived presheaf module"]
def derivedObjectCardinal (K : DerivedCategory (PresheafOfModules.{z} O)) :
    Cardinal.{max (max u v) (max w z)} :=
  sInf {kappa : Cardinal.{max (max u v) (max w z)} |
    ∃ (F : Cochain.{u, v, w, z} O) (_ : DerivedCategory.Q.obj F ≅ K),
      sectionsCardinal F ≤ kappa}

scoped[ModulesOnCategoryCardinal] notation:max "sizeD[" O "](" K ")" =>
  CategoryTheory.PresheafOfModules.Cochain.derivedObjectCardinal O K

/-- Every chosen representative bounds the least representative cardinal from above. -/
theorem derivedObjectCardinal_le_of_representation
    {K : DerivedCategory (PresheafOfModules.{z} O)}
    (F : Cochain.{u, v, w, z} O) (e : DerivedCategory.Q.obj F ≅ K) :
    derivedObjectCardinal O K ≤ sectionsCardinal F := sorry

/-- The canonical isomorphism from a subcomplex representative to the represented derived
object, obtained from an invertible localized inclusion. -/
noncomputable def representationIsoOfSubcomplex
    {K : DerivedCategory (PresheafOfModules.{z} O)}
    {F : Cochain.{u, v, w, z} O} (e : DerivedCategory.Q.obj F ≅ K)
    {G : Subobject F} (hG : IsIso (DerivedCategory.Q.map G.arrow)) :
    DerivedCategory.Q.obj (G : Cochain.{u, v, w, z} O) ≅ K :=
  @asIso _ _ _ _ (DerivedCategory.Q.map G.arrow) hG ≪≫ e

/-- The forward map of `representationIsoOfSubcomplex` is the localized inclusion followed by
the chosen representation isomorphism. -/
theorem representationIsoOfSubcomplex_hom
    {K : DerivedCategory (PresheafOfModules.{z} O)}
    {F : Cochain.{u, v, w, z} O} (e : DerivedCategory.Q.obj F ≅ K)
    {G : Subobject F} (hG : IsIso (DerivedCategory.Q.map G.arrow)) :
    (representationIsoOfSubcomplex O e hG).hom =
      DerivedCategory.Q.map G.arrow ≫ e.hom := sorry

/-- Lemma 21.43.7 (0GYY): one cardinal uniformly bounds a subcomplex of any chosen
representative which still represents the same derived object. -/
@[stacks 0GYY]
theorem exists_small_representative_subcomplex :
    ∃ kappa : Cardinal.{max (max u v) (max w z)},
      ∀ (K : DerivedCategory (PresheafOfModules.{z} O))
        (F : Cochain.{u, v, w, z} O) (_ : DerivedCategory.Q.obj F ≅ K),
        ∃ G : Subobject F,
          IsIso (DerivedCategory.Q.map G.arrow) ∧
            subcomplexCardinal G ≤ max kappa (derivedObjectCardinal O K) := sorry

/-- A subcomplex which remains a representative also bounds the least representative cardinal. -/
theorem derivedObjectCardinal_le_of_subcomplex
    {K : DerivedCategory (PresheafOfModules.{z} O)}
    {F : Cochain.{u, v, w, z} O} (e : DerivedCategory.Q.obj F ≅ K)
    {G : Subobject F} (hG : IsIso (DerivedCategory.Q.map G.arrow)) :
    derivedObjectCardinal O K ≤ subcomplexCardinal G := sorry

end CategoryTheory.PresheafOfModules.Cochain
