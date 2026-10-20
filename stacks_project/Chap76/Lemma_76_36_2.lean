module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.FiniteType
import StacksCheckRecall

/-!
# Finite fibres of relative Stein normalization

For a universally closed quasi-separated morphism of algebraic spaces which is
locally of finite type and has affine target, the relative-normalization
morphism has finite point-set fibres, and each residue-field extension of a
point of such a fibre is finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.36.2: The relative-normalization projection has finite fibres and
finite residue-field extensions when the original morphism is universally
closed, quasi-separated, locally of finite type, and has affine target. -/
@[stacks 0E1C] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.fromNormalization_fiberFinite :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [UniversallyClosed f] [QuasiSeparated f] [LocallyOfFiniteType f]
      [IsAffine Y] (y : Points Y),
      Set.Finite (fiberOver (Hom.fromNormalization f) y))

#check
  (AlgebraicGeometry.AlgebraicSpace.instModuleFiniteResidueFieldFromNormalization :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [UniversallyClosed f] [QuasiSeparated f] [LocallyOfFiniteType f]
      [IsAffine Y] (y : Points Y) (y' : fiberOver (Hom.fromNormalization f) y),
      Module.Finite (Y.residueField y) ((Hom.normalization f).residueField y'))
