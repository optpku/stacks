module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Map
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The canonical derived étale base-change map for a cartesian square with proper
vertical morphism is an isomorphism on bounded-below complexes with locally torsion
cohomology sheaves. -/
theorem derivedBaseChange_isIso_of_isProper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) E) :
    IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.derivedMapOfCommSq
      f g f' g' h_cart.toCommSq (DerivedCategory.Plus.ι.obj E)) := sorry

/-- The canonical derived étale base-change map along the chosen fibre product of a
proper morphism is an isomorphism on bounded-below complexes with locally torsion
cohomology sheaves. -/
theorem derivedBaseChange_isIso_of_isProper_pullback
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y)
    [HasPullback g f]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) E) :
    IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.derivedMapOfCommSq
      f g (pullback.fst g f) (pullback.snd g f)
      (IsPullback.of_hasPullback g f).flip.toCommSq (DerivedCategory.Plus.ι.obj E)) := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
