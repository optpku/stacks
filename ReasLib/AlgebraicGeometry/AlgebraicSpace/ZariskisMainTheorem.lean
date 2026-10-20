module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Locality

/-!
# Zariski's Main Theorem for algebraic spaces

A finite-type separated morphism of algebraic spaces is an
isomorphism over an open subspace of its relative normalization, whose inverse
image is exactly the quasi-finite locus.

A quasi-finite separated morphism of algebraic spaces factors through its
relative normalization as a quasi-compact open immersion followed by an
integral morphism, and is therefore quasi-affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- A finite-type separated morphism of algebraic spaces is an isomorphism over
an open subspace of its relative normalization, and the inverse image of this
open subspace is exactly its quasi-finite locus. -/
@[stacks 082I]
theorem FiniteType.exists_isIso_openInverseImageTo_toNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [Separated f] :
    ∃ (U' : AlgebraicSpace S) (ι : U' ⟶ normalization f)
      (hι : IsOpenImmersion ι),
      IsIso (openInverseImageTo (toNormalization f) ι) ∧
        Set.range (Points.map (openInverseImageι (toNormalization f) ι)) =
          {x | QuasiFiniteAt f x} :=
  sorry

/-- A representable finite-type separated morphism of algebraic spaces is an
isomorphism over an open subspace of its relative normalization, and the inverse
image of this open subspace is exactly its quasi-finite locus. -/
@[stacks 0ABR]
theorem exists_isIso_openInverseImageTo_toNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) [FiniteType f] [Separated f] :
    ∃ (U' : AlgebraicSpace S) (ι : U' ⟶ normalization f)
      (hι : IsOpenImmersion ι),
      IsIso (openInverseImageTo (toNormalization f) ι) ∧
        Set.range (Points.map (openInverseImageι (toNormalization f) ι)) =
          setOf (QuasiFiniteAt f) :=
  sorry

end Hom

/-- A quasi-finite separated morphism of algebraic spaces factors through its
relative normalization as a quasi-compact open immersion followed by an integral
morphism, and is quasi-affine. -/
@[stacks 0ABS]
theorem quasiFinite_separated_normalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiFinite f] [Separated f] :
    IsOpenImmersion (Hom.toNormalization f) ∧
      QuasiCompact (Hom.toNormalization f) ∧
      IsIntegralHom (Hom.fromNormalization f) ∧ QuasiAffine f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
