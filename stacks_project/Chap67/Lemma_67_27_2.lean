module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.BaseChange
import StacksCheckRecall

/-!
# Base change of the quasi-finite locus

For a locally of finite type morphism of algebraic spaces, the quasi-finite
locus is open and commutes with base change. Locally quasi-finite morphisms
in the Stacks sense, and quasi-finite morphisms, are stable under base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.27.2 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite type. The set of points
of `X` at which `f` is quasi-finite is open. The same holds for any base
change of `f`. -/
@[stacks 0ABM] #check
  (AlgebraicGeometry.AlgebraicSpace.isOpen_quasiFiniteAt :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [LocallyOfFiniteType f] → IsOpen (setOf (QuasiFiniteAt f)))

/- Lemma 67.27.2 (2): Formation of the locus where `f` is quasi-finite commutes
with base change: if `g' : X' ⟶ X` is the projection and `f' : X' ⟶ Y'` is the
base change of `f` along `g : Y' ⟶ Y`, then the quasi-finite locus of `f'` is
the preimage of the quasi-finite locus of `f`. -/
@[stacks 0ABM] #check
  (AlgebraicGeometry.AlgebraicSpace.quasiFiniteAt_locus_eq_preimage_of_isPullback :
    ∀ {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
      (hpb : IsPullback g' f' f g), [LocallyOfFiniteType f] →
        setOf (QuasiFiniteAt f') = Points.map g' ⁻¹' setOf (QuasiFiniteAt f))

/- Lemma 67.27.2 (3): The base change of a locally quasi-finite morphism of
algebraic spaces is locally quasi-finite. -/
@[stacks 0ABM] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_isStableUnderBaseChange :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S)))

/- Lemma 67.27.2 (4): The base change of a quasi-finite morphism of algebraic
spaces is quasi-finite. -/
@[stacks 0ABM] #check
  (AlgebraicGeometry.AlgebraicSpace.quasiFinite_isStableUnderBaseChange :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
      (@QuasiFinite S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : LocallyQuasiFinite f) (g : Z ⟶ Y), [HasPullback f g] →
      LocallyQuasiFinite (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.QuasiFinite.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : QuasiFinite f) (g : Z ⟶ Y), [HasPullback f g] →
      QuasiFinite (pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace
