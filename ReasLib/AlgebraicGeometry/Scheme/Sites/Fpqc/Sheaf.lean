module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- A presheaf on schemes over a base scheme is a sheaf for the fpqc topology. -/
abbrev isFpqcSheaf (S : Scheme.{u}) (F : (CategoryTheory.Over S)ᵒᵖ ⥤ Type v) : Prop :=
  Presheaf.IsSheaf (Scheme.fpqcTopology.over S) F

/-- Fpqc sheafness on schemes over a base is equivalent to Zariski sheafness
and the singleton sheaf condition for affine faithfully flat morphisms. -/
theorem isSheaf_fpqcTopology_over_iff_zariski_and_affineFaithfullyFlat
    (S : Scheme.{u}) (F : (CategoryTheory.Over S)ᵒᵖ ⥤ Type v) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) F ↔
      Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F ∧
        (∀ {U V : CategoryTheory.Over S} (f : V ⟶ U)
          [IsAffine U.left] [IsAffine V.left] [Flat f.left] [Surjective f.left],
          Presieve.IsSheafFor F (Presieve.singleton f)) := sorry

end AlgebraicGeometry
