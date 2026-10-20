module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Proper.Locality
import StacksCheckRecall

/-!
# Characterizations of proper morphisms of formal algebraic spaces

Lemma 87.31.2 records that a morphism of formal algebraic spaces is proper iff
this is tested by proper projections after scheme-valued and affine base
change, by algebraic-space properness of affine-scheme-valued fibre products,
and by a Definition 87.11.1 étale atlas of the target.
-/

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 87.31.2: properness of a morphism of formal algebraic spaces is
equivalent to the five scheme, affine, algebraic-space, and atlas conditions. -/
@[stacks 0ART] #check (AlgebraicGeometry.FormalAlgebraicSpace.Proper.tfae :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace Y] (f : X ⟶ Y),
    List.TFAE [AlgebraicGeometry.FormalAlgebraicSpace.Proper f,
      AlgebraicGeometry.FormalAlgebraicSpace.Proper.forallScheme f,
      AlgebraicGeometry.FormalAlgebraicSpace.Proper.forallAffine f,
      AlgebraicGeometry.FormalAlgebraicSpace.Proper.forallAffineAlgebraicSpace f,
      AlgebraicGeometry.FormalAlgebraicSpace.Proper.existsCoverOnTarget f])

#check (AlgebraicGeometry.FormalAlgebraicSpace.Proper.iff_forallScheme :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace Y] (f : X ⟶ Y),
    AlgebraicGeometry.FormalAlgebraicSpace.Proper f ↔
      AlgebraicGeometry.FormalAlgebraicSpace.Proper.forallScheme f)

#check (AlgebraicGeometry.FormalAlgebraicSpace.Proper.iff_forallAffine :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace Y] (f : X ⟶ Y),
    AlgebraicGeometry.FormalAlgebraicSpace.Proper f ↔
      AlgebraicGeometry.FormalAlgebraicSpace.Proper.forallAffine f)

#check (AlgebraicGeometry.FormalAlgebraicSpace.Proper.iff_forallAffineAlgebraicSpace :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace Y] (f : X ⟶ Y),
    AlgebraicGeometry.FormalAlgebraicSpace.Proper f ↔
      AlgebraicGeometry.FormalAlgebraicSpace.Proper.forallAffineAlgebraicSpace f)

#check (AlgebraicGeometry.FormalAlgebraicSpace.Proper.iff_existsCoverOnTarget :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace Y] (f : X ⟶ Y),
    AlgebraicGeometry.FormalAlgebraicSpace.Proper f ↔
      AlgebraicGeometry.FormalAlgebraicSpace.Proper.existsCoverOnTarget f)
