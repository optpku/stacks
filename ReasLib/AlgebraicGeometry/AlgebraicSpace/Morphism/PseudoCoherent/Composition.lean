module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.Composition

/-!
# Composition of pseudo-coherent morphisms of algebraic spaces

Pseudo-coherent morphisms of algebraic spaces are stable under composition.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PseudoCoherent

/-- Pseudo-coherent morphisms of algebraic spaces are stable under composition. -/
instance instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@PseudoCoherent S : MorphismProperty (AlgebraicSpace S)) where
  comp_mem f g hf hg :=
    (pseudoCoherent_iff_etaleLocal (f ≫ g)).mpr
      (etaleLocal.comp ((pseudoCoherent_iff_etaleLocal f).mp hf)
        ((pseudoCoherent_iff_etaleLocal g).mp hg))

/-- The composite of two pseudo-coherent morphisms of algebraic spaces is
pseudo-coherent. -/
@[stacks 06BT]
instance comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [PseudoCoherent f] [PseudoCoherent g] :
    PseudoCoherent (f ≫ g) :=
  MorphismProperty.comp_mem
    (@PseudoCoherent S : MorphismProperty (AlgebraicSpace S)) f g
    (inferInstance : PseudoCoherent f) (inferInstance : PseudoCoherent g)

end AlgebraicGeometry.AlgebraicSpace.PseudoCoherent
