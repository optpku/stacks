module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.ClosedImmersion.NormalExterior

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 48.15.6: for a Koszul-regular closed immersion into a quasi-compact,
quasi-separated scheme, a chosen right adjoint to derived pushforward sends the structure
sheaf to the exterior power of the normal sheaf shifted by its negative locally constant
rank. -/
@[stacks 0BR0] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.rightAdjointStructureSheaf_isNormalExteriorShift :
    ∀ {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
      (i : X ⟶ Y) [IsKoszulRegularClosedImmersion i]
      (a : AlgebraicGeometry.Scheme.DerivedQCoh Y ⥤
        AlgebraicGeometry.Scheme.DerivedQCoh X)
      (aAdjunction : AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn i ⊣ a),
      Scheme.Hom.IsNormalExteriorShift i
        (AlgebraicGeometry.IsKoszulRegularClosedImmersion.normalSheaf_isFiniteLocallyFree i)
        (a.obj (AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf Y)))

/- Under a constant-rank hypothesis, the right-adjoint image of the structure sheaf is globally
isomorphic to the corresponding fixed-rank normal exterior shift. -/
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.normalExteriorShift_isomorphic_rightAdjointStructureSheaf_of_rank :
    ∀ {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
      (i : X ⟶ Y) [IsKoszulRegularClosedImmersion i] (r : ℕ)
      [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.normalSheaf i)]
      (a : AlgebraicGeometry.Scheme.DerivedQCoh Y ⥤
        AlgebraicGeometry.Scheme.DerivedQCoh X)
      (aAdjunction : AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn i ⊣ a),
      IsIsomorphic
        (Scheme.Hom.normalExteriorShift i
          (AlgebraicGeometry.IsKoszulRegularClosedImmersion.normalSheaf_isFiniteLocallyFree i) r)
        (a.obj (AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf Y)))
