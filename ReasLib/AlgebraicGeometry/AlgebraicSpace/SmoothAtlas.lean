/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property

/-!
# Algebraic spaces from étale sheaves with smooth atlases

An étale sheaf with a representable smooth surjective map from an algebraic
space is an algebraic space. A smooth surjective map from a scheme also
suffices when the diagonal is representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An étale sheaf on schemes over `S` whose diagonal is representable by
algebraic spaces and which admits a smooth surjective morphism from a scheme
over `S` is an algebraic space. -/
@[stacks 07WF]
theorem IsAlgebraicSpace.of_etale_sheaf_smooth_surjective {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (hΔ : representableByAlgebraicSpaces (Limits.diag F)) {U : Over S}
    (p : yoneda.obj U ⟶ F)
    (hP : (representableByAlgebraicSpaces.of_diag hΔ p).has
      (@Surjective S ⊓ @Smooth S : MorphismProperty (AlgebraicSpace S))) :
    IsAlgebraicSpace F :=
  sorry

/-- An étale sheaf on schemes over `S` admitting a representable-by-algebraic-spaces,
smooth surjective morphism from an algebraic space over `S` is an algebraic space. -/
@[stacks 0GE0]
theorem IsAlgebraicSpace.of_etaleSheaf_smooth_surjective {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace U] (a : U ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Smooth S : MorphismProperty (AlgebraicSpace S)) a) :
    IsAlgebraicSpace F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
