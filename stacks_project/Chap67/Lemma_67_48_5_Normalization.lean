/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_48_8_Normalization

/-!
# Universal property of relative normalization

The constructed relative normalization of a quasi-compact and quasi-separated
morphism of algebraic spaces is initial among integral factorizations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structure morphism of the relative normalization of a quasi-compact and
quasi-separated morphism of algebraic spaces is integral. -/
instance Hom.instIsIntegralHom_fromNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    IsIntegralHom (Hom.fromNormalization f) :=
  sorry

/-- The canonical factorization of a quasi-compact and quasi-separated morphism
through `Hom.normalization` is a relative-normalization factorization. -/
theorem Hom.isNormalization_normalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    IsNormalization f (Hom.toNormalization f) (Hom.fromNormalization f) :=
  sorry

/-- Any integral factorization of a quasi-compact and quasi-separated morphism
admits a unique comparison morphism out of `Hom.normalization`. -/
theorem Hom.existsUnique_lift_fromNormalization
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (g : X ⟶ Z) (π : Z ⟶ Y)
    [IsIntegralHom π] (hf : f = g ≫ π) :
    ∃! h : Hom.normalization f ⟶ Z,
      Hom.toNormalization f ≫ h = g ∧ h ≫ π = Hom.fromNormalization f :=
  sorry

/-- The unique comparison from `Hom.normalization f` to an integral factorization
of `f` is the relative normalization of the intermediate space in the source of
`f`. -/
theorem Hom.isNormalization_lift
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (g : X ⟶ Z) (π : Z ⟶ Y)
    [IsIntegralHom π] (hf : f = g ≫ π) (h : Hom.normalization f ⟶ Z)
    (h_to : Hom.toNormalization f ≫ h = g)
    (h_from : h ≫ π = Hom.fromNormalization f) :
    IsNormalization g (Hom.toNormalization f) h :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
