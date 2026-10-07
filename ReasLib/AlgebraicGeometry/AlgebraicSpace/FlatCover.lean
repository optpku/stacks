module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!
# Flat covers of fpqc sheaves
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- There is an fpqc sheaf on schemes with representable diagonal and a
surjective, flat, universally open, quasi-compact scheme cover, but with no
representable surjective étale scheme atlas; thus the cover condition does not
force the sheaf to be an algebraic space. -/
theorem exists_fpqcSheaf_flatCover_no_etaleAtlas :
    ∃ (F : Scheme.{u}ᵒᵖ ⥤ Type u),
      Presheaf.IsSheaf Scheme.fpqcTopology F ∧
        yoneda.relativelyRepresentable (Limits.diag F) ∧
        (∃ (U : Scheme.{u}) (p : yoneda.obj U ⟶ F),
          ((@Surjective ⊓ @Flat ⊓ @UniversallyOpen ⊓ @QuasiCompact) :
              MorphismProperty Scheme).presheaf p) ∧
        ¬ (∃ (V : Scheme.{u}) (q : yoneda.obj V ⟶ F),
          ((@Etale ⊓ @Surjective) : MorphismProperty Scheme).presheaf q) := sorry

end AlgebraicGeometry.AlgebraicSpace
