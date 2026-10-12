/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Generator.Sheaf
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Topology.Sheaves.LocallySurjective
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous
import Mathlib.Tactic.CrossRefAttribute

/-!
# Dense-subsite presentations for a family of sheaves

This module records the data of a dense-subsite replacement in which a
prescribed family of sheaves becomes representable. The presentation is a
concrete data owner; its existence theorem deliberately remains
proposition-valued.
-/

@[expose] public section

open CategoryTheory Limits Opposite
open Functor.IsDenseSubsite

noncomputable section

universe u v uI

namespace CategoryTheory.Functor.DenseSubsite.Family

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {I : Type uI} (ℱ : I → Sheaf J (Type (max u v)))

/-- Concrete data for a finite-limit subcanonical dense-subsite replacement
in which a specified family of `Type (max u v)`-valued sheaves is
representable. -/
structure Presentation where
  /-- The target category of the replacement site. -/
  target : Type (max u v)
  /-- The category structure on the replacement site. -/
  [category : Category target]
  /-- The topology on the replacement site. -/
  topology : GrothendieckTopology target
  /-- The replacement topology is subcanonical. -/
  [subcanonical : topology.Subcanonical]
  /-- The replacement site has finite limits. -/
  [finiteLimits : HasFiniteLimits target]
  /-- The comparison functor from the original site. -/
  comparison : C ⥤ target
  /-- The comparison exhibits the original site as a dense subsite. -/
  [denseSubsite : comparison.IsDenseSubsite J topology]
  /-- Covering presieves are exactly locally-surjective representable
  coproduct presentations. -/
  covers :
    ∀ ⦃X : target⦄ (R : Presieve X),
      R ∈ topology.toPrecoverage X ↔
        ∃ (ι : Type (max u v)) (Y : ι → target) (π : ∀ i, Y i ⟶ X),
          R = Presieve.ofArrows Y π ∧
            Presheaf.IsLocallySurjective topology
              (Limits.Sigma.desc (fun i ↦ (topology.yoneda.map (π i)).hom))
  /-- Every subobject of a representable sheaf is representable. -/
  subobjects :
    ∀ X : target, ∀ G : Subobject (topology.yoneda.obj X),
      ((G : Sheaf topology (Type (max u v))).obj).IsRepresentable
  /-- The prescribed source family is representable after dense-subsite
  transport. -/
  family : ∀ i : I,
    (((sheafEquiv J topology comparison (Type (max u v))).functor.obj (ℱ i)).obj).IsRepresentable
  /-- If the source topology is subcanonical, the comparison functor is fully
  faithful. -/
  fullyFaithful : J.Subcanonical → comparison.FullyFaithful

attribute [instance] Presentation.category
attribute [instance] Presentation.subcanonical
attribute [instance] Presentation.finiteLimits
attribute [instance] Presentation.denseSubsite

namespace Presentation

/-- The special-cocontinuity comparison supplied by a dense-subsite
presentation. -/
theorem specialCocontinuous (P : Presentation J ℱ) :
    P.comparison.IsSpecialCocontinuous J P.topology := sorry

/-- The canonical transport of set-valued sheaves to the replacement site. -/
noncomputable abbrev transport (P : Presentation J ℱ) :
    Sheaf J (Type (max u v)) ⥤ Sheaf P.topology (Type (max u v)) :=
  (sheafEquiv J P.topology P.comparison (Type (max u v))).functor

/-- A prescribed family member is representable after transport to the
replacement site. -/
theorem familyIsRepresentable (P : Presentation J ℱ) (i : I) :
    ((P.transport).obj (ℱ i)).obj.IsRepresentable := sorry

/-- The source-facing package of subcanonicality, finite limits, comparison,
covering, subobject, family, and full-faithfulness properties of a
presentation. -/
theorem spec (P : Presentation J ℱ) :
    P.topology.Subcanonical ∧
      HasFiniteLimits P.target ∧
      P.comparison.IsSpecialCocontinuous J P.topology ∧
      P.comparison.IsDenseSubsite J P.topology ∧
      (∀ ⦃X : P.target⦄ (R : Presieve X),
        R ∈ P.topology.toPrecoverage X ↔
          ∃ (ι : Type (max u v)) (Y : ι → P.target) (π : ∀ i, Y i ⟶ X),
            R = Presieve.ofArrows Y π ∧
              Presheaf.IsLocallySurjective P.topology
                (Limits.Sigma.desc (fun i ↦ (P.topology.yoneda.map (π i)).hom))) ∧
      (∀ X : P.target, ∀ G : Subobject (P.topology.yoneda.obj X),
        ((G : Sheaf P.topology (Type (max u v))).obj).IsRepresentable) ∧
      (∀ i : I, ((P.transport).obj (ℱ i)).obj.IsRepresentable) ∧
      (∀ h : J.Subcanonical, Nonempty P.comparison.FullyFaithful) := sorry

/-- Lemma 7.29.5 (03CI): every small family of set-valued sheaves admits a
finite-limit, subcanonical dense-subsite presentation with the stated
representability properties. -/
@[stacks 03CI]
theorem nonempty [HasWeakSheafify J (Type (max u v))] [Small.{max u v} I] :
    Nonempty (Presentation J ℱ) := sorry

end Presentation

end CategoryTheory.Functor.DenseSubsite.Family
