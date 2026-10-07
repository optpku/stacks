module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap80.Definition_80_4_1_Relative

/-!
# Representability of the diagonal by schemes from an fppf algebraic-space atlas

An fppf sheaf on schemes over `S` that admits a map from an algebraic space
which is representable by algebraic spaces, surjective, flat, and locally of
finite presentation has diagonal representable by schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 80.5.3: let `S` be a scheme. Let `F : (Over S)ᵒᵖ ⥤ Type u` be a
functor. Assume that `F` is a sheaf for the fppf topology, and that there is an
algebraic space `X` together with a map `X ⟶ F` which is representable by
algebraic spaces, surjective, flat, and locally of finite presentation. Then
the diagonal `diag F : F ⟶ F ⨯ F` is representable by schemes. -/
@[stacks 046K]
theorem relativelyRepresentable_diag {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a) :
    yoneda.relativelyRepresentable (diag F) :=
  sorry

/-- Every map from a scheme over `S` to an fppf sheaf admitting an algebraic-space
atlas that is representable by algebraic spaces, surjective, flat, and locally of
finite presentation is representable by schemes. -/
theorem relativelyRepresentable_yoneda {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a)
    ⦃T : Over S⦄ (ξ : yoneda.obj T ⟶ F) :
    yoneda.relativelyRepresentable ξ :=
  sorry

/-- Pairwise fibre products of Yoneda sections of an fppf sheaf admitting an
algebraic-space atlas that is representable by algebraic spaces, surjective,
flat, and locally of finite presentation are representable. -/
theorem isRepresentable_pullback {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a)
    ⦃T T' : Over S⦄ (ξ : yoneda.obj T ⟶ F) (ξ' : yoneda.obj T' ⟶ F) :
    (pullback ξ ξ').IsRepresentable :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
