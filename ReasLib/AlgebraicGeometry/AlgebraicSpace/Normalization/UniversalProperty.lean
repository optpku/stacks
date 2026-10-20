module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization

/-!
# Universal property of relative normalization

The constructed relative normalization of a quasi-compact and quasi-separated
morphism of algebraic spaces is initial among integral factorizations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open AlgebraicGeometry.AlgebraicSpace.Hom (fromNormalization)

/-- The structure morphism of the relative normalization of a quasi-compact and
quasi-separated morphism of algebraic spaces is integral. -/
instance IsIntegralHom.fromNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    IsIntegralHom (fromNormalization f) :=
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
