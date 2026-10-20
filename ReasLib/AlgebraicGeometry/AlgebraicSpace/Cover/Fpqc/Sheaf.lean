module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fpqc
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace

namespace FpqcCovering

/-- An fpqc covering family is a sheaf-for presieve for every representable
presheaf given by an algebraic space over the base scheme. -/
@[stacks 04P2]
theorem isSheafFor_yoneda {S : Scheme.{u}} {T : AlgebraicSpace S} {ι : Type v}
    {family : ι → Over T} (hfamily : FpqcCovering family)
    (B : AlgebraicSpace S) :
    Presieve.IsSheafFor (yoneda.obj B)
      (Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom)) :=
  sorry

/-- Compatible morphisms from the members of an fpqc covering family glue to a
unique morphism from its target. -/
theorem existsUnique_hom {S : Scheme.{u}} {T : AlgebraicSpace S} {ι : Type v}
    {family : ι → Over T} (hfamily : FpqcCovering family)
    {B : AlgebraicSpace S} (g : (i : ι) → (family i).left ⟶ B)
    (hcompat : ∀ i j,
      pullback.fst (family i).hom (family j).hom ≫ g i =
        pullback.snd (family i).hom (family j).hom ≫ g j) :
    ∃! f : T ⟶ B, ∀ i, (family i).hom ≫ f = g i :=
  sorry

/-- Every representable presheaf with values in any universe satisfies the
sheaf condition for an fpqc covering family. -/
theorem isSheafFor_of_isRepresentable {S : Scheme.{u}}
    {P : (AlgebraicSpace S)ᵒᵖ ⥤ Type w} [P.IsRepresentable]
    {T : AlgebraicSpace S} {ι : Type v} {family : ι → Over T}
    (hfamily : FpqcCovering family) :
    Presieve.IsSheafFor P
      (Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom)) :=
  sorry

/-- The presieve associated to an fpqc covering family is effective
epimorphic. -/
theorem effectiveEpimorphic {S : Scheme.{u}} {T : AlgebraicSpace S} {ι : Type v}
    {family : ι → Over T} (hfamily : FpqcCovering family) :
    (Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom)).EffectiveEpimorphic :=
  sorry

end FpqcCovering

end AlgebraicGeometry.AlgebraicSpace
