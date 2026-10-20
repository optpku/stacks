module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicStack.DeligneMumford.Atlas
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Atlas
import StacksCheckRecall

/-!
# Unramified or locally quasi-finite fppf covers imply DM or quasi-DM

A surjective, flat, locally finitely presented morphism from an algebraic
space to an algebraic stack that is unramified (equivalently étale) implies
the target is DM, and the locally quasi-finite case implies quasi-DM.
-/

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

#check (AlgebraicGeometry.Groupoids.Hom.Etale.of_unramified :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [Groupoids.Hom.Flat f] [Groupoids.Hom.LocallyOfFinitePresentation f],
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S) f → Groupoids.Hom.Etale f)

#check (AlgebraicGeometry.DeligneMumfordStack.of_unramified :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {W : AlgebraicSpace S} (f : W.toGroupoids ⟶ X)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f],
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S) f → DeligneMumfordStack X)

/- Lemma 101.4.14 (1): Let `X` be an algebraic stack. Let `W` be an algebraic
space, and let `f : W.toGroupoids ⟶ X` be a surjective, flat, locally finitely
presented morphism. If `f` is unramified (i.e., étale, i.e., `X` is
Deligne-Mumford), then `X` is DM. -/
@[stacks 06MB] #check (AlgebraicGeometry.AlgebraicStack.IsDM.of_unramified :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {W : AlgebraicSpace S} (f : W.toGroupoids ⟶ X)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f],
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S) f → AlgebraicStack.IsDM X)

/- Lemma 101.4.14 (2): Let `X` be an algebraic stack. Let `W` be an algebraic
space, and let `f : W.toGroupoids ⟶ X` be a surjective, flat, locally finitely
presented morphism. If `f` is locally quasi-finite, then `X` is quasi-DM. -/
@[stacks 06MB] #check (AlgebraicGeometry.AlgebraicStack.IsQuasiDM.of_locallyQuasiFinite :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {W : AlgebraicSpace S} (f : W.toGroupoids ⟶ X)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f],
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) f →
      AlgebraicStack.IsQuasiDM X)
