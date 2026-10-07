module

public import ReasLib.AlgebraicTopology.SimplicialObject.Evaluation.Product
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Presheaf.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Model
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Point
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived lower-shriek and tensor

This leaf owns the module-valued tensor comparison for the presheaf presentation of a category
over a point.  In the Stacks application this is the chaotic-topology presentation of
`D(underline B)`.  The source and target operations are the canonical two-variable derived
tensors, rather than an arbitrary monoidal structure on a chosen derived category.  The pointlike
cosimplicial object is retained as an explicit hypothesis; its diagonal reindexing is the bridge
used in the proof.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe q u v w

namespace CategoryTheory.DerivedColimit.Tensor

section Module

variable {C : Type u} [Category.{v} C]
variable {B : Type w} [CommRing B]
variable [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]
variable [HasDerivedCategory.{q} (ModuleCat.Presheaf C B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived C (ModuleCat B) :
    HomotopyCategory (ModuleCat.Presheaf C B) (up ℤ) ⥤ DerivedCategory (ModuleCat B))
  (HomotopyCategory.quasiIso (ModuleCat.Presheaf C B) (up ℤ))]

/-- Lemma 21.39.10 (08QC), presheaf witness form: a pointlike cosimplicial object makes derived
colimit commute with the canonical two-variable derived tensor.  For the chaotic topology this is
the presheaf presentation of the lower-shriek statement for `D(underline B)`.  The diagonal
pointlike object is supplied by `CosimplicialObject.Pointlike.hasHomSpaces_diag`.
-/
@[stacks 08QC "pointlike derived lower-shriek tensor comparison"]
theorem tensor_isomorphic_of_pointlike
    (Ubullet : CosimplicialObject C)
    (hUbullet : CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
    (K₁ K₂ : DerivedCategory (ModuleCat.Presheaf C B)) :
    IsIsomorphic
      ((categoryOverPointDerivedColimit C (ModuleCat B)).obj
        (DerivedCategory.DerivedTensor.Bifunctor.obj K₁ K₂))
      (DerivedCategory.DerivedTensor.Bifunctor.obj
        ((categoryOverPointDerivedColimit C (ModuleCat B)).obj K₁)
        ((categoryOverPointDerivedColimit C (ModuleCat B)).obj K₂)) := sorry

/-- Lemma 21.39.10 (08QC), presheaf source form: the comparison holds whenever a pointlike
cosimplicial object exists.  This is the reusable chaotic-presheaf specialization; the sheaf-side
source notation is related to it by the chaotic sheaf-presheaf equivalence. -/
@[stacks 08QC "existential pointlike derived lower-shriek tensor comparison"]
theorem tensor_isomorphic_of_exists_pointlike
    (hUbullet : ∃ Ubullet : CosimplicialObject C,
      CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
    (K₁ K₂ : DerivedCategory (ModuleCat.Presheaf C B)) :
      IsIsomorphic
      ((categoryOverPointDerivedColimit C (ModuleCat B)).obj
        (DerivedCategory.DerivedTensor.Bifunctor.obj K₁ K₂))
      (DerivedCategory.DerivedTensor.Bifunctor.obj
        ((categoryOverPointDerivedColimit C (ModuleCat B)).obj K₁)
        ((categoryOverPointDerivedColimit C (ModuleCat B)).obj K₂)) := sorry

/-- The pointlike tensor comparison for an explicit two-variable derived tensor model.  This
version keeps the selected target-side model as data, so downstream constructions can name
their target computation explicitly instead of relying on a hidden global model choice. -/
@[stacks 08QC "pointlike derived lower-shriek tensor comparison for an explicit model"]
theorem tensor_isomorphic_of_pointlike_model
    (M : DerivedCategory.DerivedTensor.Bifunctor.Model (C := ModuleCat.{w} B))
    (Ubullet : CosimplicialObject C)
    (hUbullet : CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
    (K₁ K₂ : DerivedCategory (ModuleCat.Presheaf C B)) :
    IsIsomorphic
      ((categoryOverPointDerivedColimit C (ModuleCat B)).obj
        (DerivedCategory.DerivedTensor.Bifunctor.obj K₁ K₂))
      (M.obj
        ((categoryOverPointDerivedColimit C (ModuleCat B)).obj K₁)
        ((categoryOverPointDerivedColimit C (ModuleCat B)).obj K₂)) := sorry

end Module

end CategoryTheory.DerivedColimit.Tensor
