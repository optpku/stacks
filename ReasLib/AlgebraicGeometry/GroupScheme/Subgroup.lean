/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.MorphismProperty.Comma

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A closed subgroup scheme of the group scheme `G` over `S`. -/
abbrev ClosedSubgroup {S : Scheme.{u}} (G : Over S) [GrpObj G] : Type (u + 1) :=
  MorphismProperty.Over
    (MorphismProperty.inverseImage @IsClosedImmersion
      (Grp.forget (Over S) ⋙ Over.forget S)) ⊤ (Grp.mk G)

/-- An open subgroup scheme of the group scheme `G` over `S`. -/
abbrev OpenSubgroup {S : Scheme.{u}} (G : Over S) [GrpObj G] : Type (u + 1) :=
  MorphismProperty.Over
    (MorphismProperty.inverseImage @IsOpenImmersion
      (Grp.forget (Over S) ⋙ Over.forget S)) ⊤ (Grp.mk G)

namespace ClosedSubgroup

variable {S : Scheme.{u}} {G H : Over S} [GrpObj G] [GrpObj H]

/-- The inclusion in `Over S` underlying a closed subgroup scheme. -/
abbrev inclusion (K : ClosedSubgroup G) : K.left.X ⟶ G :=
  K.hom.hom.hom

/-- Construct a closed subgroup scheme from a group-object morphism whose underlying scheme
morphism is a closed immersion. -/
noncomputable def mk (i : H ⟶ G) [IsMonHom i] [IsClosedImmersion i.left] :
    ClosedSubgroup G :=
  MorphismProperty.Over.mk ⊤ (Grp.ofHom i) (inferInstance : IsClosedImmersion i.left)

/-- The underlying scheme inclusion of a closed subgroup scheme is a closed immersion. -/
instance isClosedImmersion (K : ClosedSubgroup G) :
    IsClosedImmersion K.inclusion.left := K.prop

/-- The defining group-homomorphism and closed-immersion conditions of a closed subgroup
scheme. -/
theorem spec (K : ClosedSubgroup G) :
    IsMonHom K.hom.hom.hom ∧ IsClosedImmersion K.hom.hom.hom.left := by
  exact ⟨inferInstance, K.isClosedImmersion⟩

/-- The group-object morphism underlying a closed subgroup made from `i` is `i`. -/
@[simp]
theorem mk_hom (i : H ⟶ G) [IsMonHom i] [IsClosedImmersion i.left] :
    (mk i).hom.hom.hom = i := rfl

end ClosedSubgroup

namespace OpenSubgroup

variable {S : Scheme.{u}} {G H : Over S} [GrpObj G] [GrpObj H]

/-- The inclusion in `Over S` underlying an open subgroup scheme. -/
abbrev inclusion (K : OpenSubgroup G) : K.left.X ⟶ G :=
  K.hom.hom.hom

/-- Construct an open subgroup scheme from a group-object morphism whose underlying scheme
morphism is an open immersion. -/
noncomputable def mk (i : H ⟶ G) [IsMonHom i] [IsOpenImmersion i.left] :
    OpenSubgroup G :=
  MorphismProperty.Over.mk ⊤ (Grp.ofHom i) (inferInstance : IsOpenImmersion i.left)

/-- The underlying scheme inclusion of an open subgroup scheme is an open immersion. -/
instance isOpenImmersion (K : OpenSubgroup G) :
    IsOpenImmersion K.inclusion.left := K.prop

/-- The defining group-homomorphism and open-immersion conditions of an open subgroup scheme. -/
theorem spec (K : OpenSubgroup G) :
    IsMonHom K.hom.hom.hom ∧ IsOpenImmersion K.hom.hom.hom.left := by
  exact ⟨inferInstance, K.isOpenImmersion⟩

/-- The group-object morphism underlying an open subgroup made from `i` is `i`. -/
@[simp]
theorem mk_hom (i : H ⟶ G) [IsMonHom i] [IsOpenImmersion i.left] :
    (mk i).hom.hom.hom = i := rfl

end OpenSubgroup

end AlgebraicGeometry.Scheme
