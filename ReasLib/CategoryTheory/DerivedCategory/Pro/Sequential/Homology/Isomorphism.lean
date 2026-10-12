/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Pro.Sequential.Homology.Value
public import ReasLib.CategoryTheory.Pro.Sequential.Isomorphism
public import ReasLib.CategoryTheory.Pro.Sequential.Quotient.NatTrans

/-!
# Homology detection of bounded sequential derived pro-isomorphisms

For uniformly bounded sequential derived towers, the canonical pro-morphism is invertible exactly
when its maps on the finitely many relevant homology towers are invertible.
-/

@[expose] public section

open CategoryTheory

universe w u v

namespace CategoryTheory.DerivedCategory.Pro.Sequential.Homology

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Lemma 13.42.5 (0G3D): a morphism of uniformly bounded sequential derived towers induces an
isomorphism of associated pro-objects when every homology morphism in the bounding interval does. -/
@[stacks 0G3D]
theorem toHom_isIso
    {X Y : SequentialInverseSystem (DerivedCategory A)} (α : X ⟶ Y) (a b : ℤ)
    (hX : IsUniformlyBounded X a b) (hY : IsUniformlyBounded Y a b)
    (hH : ∀ i ∈ Set.Icc a b,
      IsIso (((CategoryTheory.Pro.SequentialHom.ofNatTrans α).map
        (DerivedCategory.homologyFunctor A i)).toHom)) :
    IsIso ((CategoryTheory.Pro.SequentialHom.ofNatTrans α).toHom) := sorry

/-- The canonical common-refinement class of the tower morphism has invertible associated
pro-morphism under the same bounded homology criterion. -/
@[stacks 0G3D "common-refinement quotient"]
theorem quotientToHom_isIso
    {X Y : SequentialInverseSystem (DerivedCategory A)} (α : X ⟶ Y) (a b : ℤ)
    (hX : IsUniformlyBounded X a b) (hY : IsUniformlyBounded Y a b)
    (hH : ∀ i ∈ Set.Icc a b,
      IsIso (((CategoryTheory.Pro.SequentialHom.ofNatTrans α).map
        (DerivedCategory.homologyFunctor A i)).toHom)) :
    IsIso (CategoryTheory.Pro.SequentialHom.quotientToHom
      (CategoryTheory.Pro.SequentialHom.Quotient.ofNatTrans α)) := sorry

/-- The pro-isomorphism in Lemma 13.42.5 has a concrete representative inverse after common
refinement. -/
@[stacks 0G3D "representative inverse"]
theorem hasRepresentativeInverse
    {X Y : SequentialInverseSystem (DerivedCategory A)} (α : X ⟶ Y) (a b : ℤ)
    (hX : IsUniformlyBounded X a b) (hY : IsUniformlyBounded Y a b)
    (hH : ∀ i ∈ Set.Icc a b,
      IsIso (((CategoryTheory.Pro.SequentialHom.ofNatTrans α).map
        (DerivedCategory.homologyFunctor A i)).toHom)) :
    (CategoryTheory.Pro.SequentialHom.ofNatTrans α).HasRepresentativeInverse := sorry

/-- Under common uniform bounds, homology in the bounding interval detects whether the
sequential pro-morphism induced by a natural transformation is an isomorphism. -/
@[stacks 0G3D]
theorem toHom_isIso_iff
    {X Y : SequentialInverseSystem (DerivedCategory A)} (α : X ⟶ Y) (a b : ℤ)
    (hX : IsUniformlyBounded X a b) (hY : IsUniformlyBounded Y a b) :
    IsIso ((CategoryTheory.Pro.SequentialHom.ofNatTrans α).toHom) ↔
      ∀ i ∈ Set.Icc a b,
        IsIso (((CategoryTheory.Pro.SequentialHom.ofNatTrans α).map
          (DerivedCategory.homologyFunctor A i)).toHom) := sorry

end CategoryTheory.DerivedCategory.Pro.Sequential.Homology
