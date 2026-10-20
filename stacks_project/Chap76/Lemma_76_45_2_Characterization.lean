module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Relative.Etale
public import stacks_project.Chap75.Lemma_75_26_4_Pullback

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsMPseudoCoherentOver.onEtaleSquare :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
 {f : X ⟶ Y}
    (sq : EtaleSquare f)
    [AlgebraicGeometry.LocallyOfFiniteType sq.map.left]
    (E : ModuleDerived X) (m : ℤ), Prop)
