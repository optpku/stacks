module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Ext
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsRegularClosedImmersion

/- Lemma 50.17.4: for a regular closed immersion of codimension `c`, Ext from the
pushforward of any source module to a locally free target module vanishes in degrees below
`c`. -/
@[stacks 0G5I] #check
  (AlgebraicGeometry.IsRegularClosedImmersion.extPushforwardSubsingleton :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsRegularClosedImmersion i]
      (c : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
      (F : Z.Modules) (E : X.Modules) [E.IsLocallyFree] (q : ℕ) (hq : q < c),
      Subsingleton (@CategoryTheory.Abelian.Ext X.Modules inferInstance inferInstance
        (@CategoryTheory.IsGrothendieckAbelian.hasExt X.Modules inferInstance inferInstance
          (SheafOfModules.isGrothendieckAbelian X.ringCatSheaf))
        ((Scheme.Modules.pushforward i).obj F) E q))

end AlgebraicGeometry.IsRegularClosedImmersion
