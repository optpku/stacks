module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.FppfDiagonal
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 80.5.3: let `S` be a scheme. Let `F : (Over S)ᵒᵖ ⥤ Type u` be a
functor. Assume that `F` is a sheaf for the fppf topology, and that there is an
algebraic space `X` together with a map `X ⟶ F` which is representable by
algebraic spaces, surjective, flat, and locally of finite presentation. Then
the diagonal `diag F : F ⟶ F ⨯ F` is representable by schemes. -/
@[stacks 046K] #check
  (AlgebraicGeometry.AlgebraicSpace.relativelyRepresentable_diag :
    ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a),
    yoneda.relativelyRepresentable (Limits.diag F))

#check
  (AlgebraicGeometry.AlgebraicSpace.relativelyRepresentable_yoneda :
    ∀ {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a)
    ⦃T : Over S⦄ (ξ : yoneda.obj T ⟶ F),
    yoneda.relativelyRepresentable ξ)

#check
  (AlgebraicGeometry.AlgebraicSpace.isRepresentable_pullback :
    ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a)
    ⦃T T' : Over S⦄ (ξ : yoneda.obj T ⟶ F) (ξ' : yoneda.obj T' ⟶ F),
    (pullback ξ ξ').IsRepresentable)

end AlgebraicGeometry.AlgebraicSpace
